#!/bin/sh

# This script is used to generate the templates for the guide
SCRIPT_NAME="$0"
SED=$(command -v gsed || command -v sed)

function usage() {
    echo "Usage: $SCRIPT_NAME --mode <MODE>"
    echo "<MODE> is the mode to run the script in. It can be one of the following:"
    echo "  - check: checks if the templates are up to date"
    echo "  - update: updates the templates"
    echo "Use --help to print the usage"
    exit 1
}

missing() {
  >&2 echo "Missing $1 parameter. Please check if all parameters were specified."
  >&2 usage
}

while test $# -gt 0; do
  case "$1" in
    help)
      usage
      ;;
    --mode)
      shift
      if test $# -gt 0; then
        MODE=$1
      else
        missing "MODE"
      fi
      shift
      ;;
      *)
      usage
      ;;
  esac
done

if [ "$MODE" != "check" ] && [ "$MODE" != "update" ]; then
    >&2 echo "Incorrect mode specified."
    usage
fi

HELP_DIR="./guide/src/templates/help_templates/"
COMMAND_DIR="./guide/src/templates/commands/hermes/"
TMP_PATH="/tmp/hermes_mdbook_templates"
OUTPUT=0

function print_array_with_prefix() {
    # Prints every element of the array given as argument prefixed by $1.
    # Args :
    # - $1 : Prefix to use
    # - $2 : Array to print
    prefix=$1
    shift
    for i in "$@"; do
        if [ $i != "help" ]; then
            echo $prefix"/"$i
        fi
    done
}

function print_array() {
    # Prints every element of the array given as argument.
    # Args :
    # - $1 : Array to print
    for i in "$@"; do
        echo "$i"
    done
}

function generate_commands_rec(){
    # Called by generate_commands to generate every command or Hermes.
    # Echo all the subcommands of the commands given by $2.
    # Args :
    # - $1: Command prefix with whitespaces replaced by '/'
    # - $2: Beginning of the array of commands
    local cmd_prefix=$(echo $1 | $SED 's/\// /g')
    shift
    for command in "$@"; do
        # Since there is no delimiter between two subcommands, a trick can be to cut the line up to the N-th character
        if [ $command = "fee" ]; then
            # The fee command needs a longer cut than the others
            local cut=31
        elif [ $command = "tx" ]; then
            # The tx command needs a longer cut than the others
            local cut=25
        else
            local cut=19
        fi

        # if command is not help and not empty then echo its subcommands and call the function recursively
        if [ "$command" != "help" ] && [ ! -z "$command" ]; then
            local new_commands=$(cargo run -q --bin hermes $cmd_prefix $command --help | $SED '0,/^SUBCOMMANDS:.*/d' | cut -c 1-$cut | $SED '/^\s*$/d ; s/\s\+\(\S\+\)\s*.*/\1/')
            if [ -z "$cmd_prefix" ]; then
                local new_cmd_prefix=$command
            else
                local new_cmd_prefix=$(echo $cmd_prefix"/"$command | $SED 's/ /\//g')
            fi
            if [ ! -z "$new_commands" ]; then
                print_array_with_prefix $new_cmd_prefix $new_commands
                generate_commands_rec $new_cmd_prefix $new_commands &
            fi
            wait
        fi
    done
}

function generate_commands(){
    # Generates the list of every commands of Hermes
    echo "version"  # Special case
    local new_commands=$(cargo run -q --bin hermes help | $SED '0,/^SUBCOMMANDS:.*/d ; s/\s\+\(\S\+\)\s*.*/\1/')
    print_array $new_commands
    generate_commands_rec "" $new_commands
}

function generate_help(){
    # - In "update" mode, it will generate the help for each command and store it in the
    # corresponding file in the $HELP_DIR directory.
    #
    # - In "check" mode, it will verify that the help files are up to date.
    #
    # Args :
    # - $1 : Array of commands where subcommands are separated by '/'. (e.g. ["query/channels", "config"])
    if [ $MODE = "update" ]; then
        echo "Updating help templates. If any file is modified, please modify the guide accordingly."
    else
        echo "Checking if help templates are up to date."
    fi
    for path in "$@"; do
        command=$(echo "$path" | $SED -e 's/\// /g')

        # help commands are edge cases
        if [ $path != "help" ]; then
            local command=$(echo "$path" | $SED -e 's/\// /g')" --help"
        else
            local command="help"
        fi

        # Check that the command is not empty
        if [ ! -z "$path" ]; then
            # Create the directory (if they don't exist) and the file
            filename="$HELP_DIR$path.md"
            dir="${filename%/*}"
            mkdir -p $dir

            cargo run -q --bin hermes $command | $SED '1s/.*/DESCRIPTION:/' > $TMP_PATH
            if ! cmp -s $TMP_PATH $filename; then
                if [ $MODE = "update" ]; then
                    mv $TMP_PATH $filename
                    echo "$filename was updated."
                else
                    >&2 echo "$filename is not up to date."
                    OUTPUT=1
                fi
            fi
        fi
    done
}

function generate_templates(){
    # - In update mode, it generates templates from the USAGE section of the help and stores it in the
    # corresponding file in the $COMMAND_DIR directory.
    # - In check mode, it will verify that the template files are up to date.
    #
    # Args :
    # - $1 : Array of commands where subcommands are separated by '/'. (e.g. ["query/channels", "config"])
    if [ $MODE = "update" ]; then
        echo "Updating templates. If any file is modified, please modify the guide accordingly."
    else
        echo "Checking if templates are up to date."
    fi
    for path in "$@"; do
            # help commands are edge cases
            if [ $path != "help" ]; then
                local command=$(echo "$path" | $SED -e 's/\// /g')" --help"
            else
                local command="help"
            fi

            # Create the directory (if they don't exist) and the file
            local tmp="$COMMAND_DIR$path"
            local dir="${tmp%/*}"
            mkdir -p $dir

            local cpt=1
            cargo run -q --bin hermes $command | $SED -n '/USAGE:/, /OPTIONS:/{ /USAGE:/! { /OPTIONS:/! p }}'  | $SED -r '/^\s*$/d ; s/^\s+// ; s/</[[#/g ; s/>/]]/g; s/hermes/[[#BINARY hermes]][[#GLOBALOPTIONS]]/ ; s/ \[(OPTIONS|SUBCOMMAND)]/\[\[#\1]]/g ;' | while read line || [[ -n $line ]]
            do
                # Create a template for every usage
                filename=$COMMAND_DIR$path"_$cpt.md"
                echo -n $line > $TMP_PATH
                local cpt=$((cpt+1))
                if ! cmp -s $TMP_PATH $filename; then
                    if [ $MODE = "update" ]; then
                        mv $TMP_PATH $filename
                        echo "$filename was updated."
                    else
                        >&2 echo "$filename is not up to date."
                        OUTPUT=1
                    fi
                fi
            done
    done
}

function is_gnu_sed() {
    $SED --version > /dev/null 2>&1
}

# BSD sed does not have a --version option: https://www.freebsd.org/cgi/man.cgi?query=sed&sektion=&n=1
# GNU sed has a --version option: https://www.gnu.org/software/sed/manual/sed.pdf
if ! is_gnu_sed ; then
    echo "WARNING: gsed unavailable, using not GNU sed"
fi

commands=$(generate_commands)
generate_help $commands
generate_templates $commands

exit $OUTPUT
