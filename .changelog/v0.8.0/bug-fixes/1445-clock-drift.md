- Fix for client state clock drift [#1445]:
    * Added new config param `max_clock_drift` to prevent
    the problem for appearing in newly-created clients.
    * Added a synchronos waiting in client update logic
    to allow destination chain to reach a new height
    before submitting a client update message.


[#1445]: https://github.com/informalsystems/ibc-rs/issues/1445
