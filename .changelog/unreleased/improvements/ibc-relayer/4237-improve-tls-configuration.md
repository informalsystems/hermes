- Only configure TLS if the scheme is HTTPS and if the endpoint is
  IPv6, parse the endpoint to remove the brackets before setting it
  as domain name.
  ([\#4237](https://github.com/informalsystems/hermes/issues/4237))