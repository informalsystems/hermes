1.
$ hermes scan

2. Outputs all scanned channels into `paths.json`

3. Filter `paths.json` however you like
   eg. with `jq` or with `hermes filter paths.json -f my_filter.dsl`

4.
$ hermes start --paths=paths.json

5. Hermes watches the `paths.json` file


