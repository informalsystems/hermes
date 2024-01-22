- The `type` key in the `[[chains]]` section is now required. ([\#3636](https://github.com/informalsystems/hermes/issues/3636))
  If you previously did not specify that key, you must now set it to `type = "CosmosSdk"`, eg.

  ```rust
  [[chains]]
  id   = "osmosis-1"
  type = "CosmosSdk"
  ``` 
