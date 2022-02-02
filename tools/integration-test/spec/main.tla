---- MODULE main ----

EXTENDS transfer

OsmosisTest ==
    /\ "ixo" \in DOMAIN chains["osmosis"].bank["akash"]
    /\ chains["osmosis"].bank["akash"]["ixo"] = 2

Invariant == ~OsmosisTest

====