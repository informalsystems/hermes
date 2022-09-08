#!/bin/sh

# This script is used to generate the templates for the guide

HELP_DIR="./guide/src/templates/commands/hermes/help/"

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
        if [ $i != "help" ]; then
            echo "$i"
        fi
    done
}

function generate_commands_rec(){
    # Called by generate_commands to generate every command or Hermes. 
    # Echo all the subcommands of the commands given by $2.
    # Args : 
    # - $1: Command prefix with whitespaces replaced by '/'
    # - $2: Beginning of the array of commands
    local cmd_prefix=$(echo $1 | sed 's/\// /g')
    shift
    for command in "$@"; do
        # Since there is no delimiter between two subcommands, a trick can be to cut the line up to the N-th character
        if [ $command = "tx" ]; then
            # The tx command needs a longer cut than the others
            local cut=25
        else 
            local cut=19
        fi
        # if command is not help and not empty then echo its subcommands and call the function recursively
        if [ "$command" != "help" ] && [ ! -z "$command" ]; then
            local new_commands=$(cargo run -q --bin hermes $cmd_prefix $command --help | sed '0,/^SUBCOMMAND.*/d' | cut -c 1-$cut | sed '/^\s*$/d' | sed 's/\s\+\(\S\+\)\s*.*/\1/')
            if [ -z "$cmd_prefix" ]; then
                local new_cmd_prefix=$command
            else
                local new_cmd_prefix=$(echo $cmd_prefix"/"$command | sed 's/ /\//g')
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
    local new_commands=$(cargo run -q --bin hermes help | sed '0,/^SUBCOMMAND.*/d' | sed 's/\s\+\(\S\+\)\s*.*/\1/')
    print_array $new_commands
    generate_commands_rec "" $new_commands
}

function generate_help(){
    # This command expects an array of commands as arguments where subcommands are separated by '/'
    # (e.g. ["query/channels", "config"]). It will generate the help for each command and store it in the
    # corresponding file.
    for path in "$@"; do
        command=$(echo "$path" | sed -e 's/\// /g')
        # Check that the command is not empty
        if [ ! -z "$path" ]; then
            # Create the directory (if they don't exist) and the file
            filename="$HELP_DIR$path.md"
            dir="${filename%/*}"
            mkdir -p $dir
            cargo run -q --bin hermes $command --help | sed '1s/.*/DESCRIPTION:/' > $filename &
        fi
    done
    wait
}

commands=$(generate_commands)
echo $commands
generate_help $commands
