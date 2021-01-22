----------------- MODULE ICS02TwoChainsEnvironment_apalache -----------------

EXTENDS ICS02TwoChainsEnvironment

OVERRIDE_MaxHeight == 4
OVERRIDE_NrClientsChainA == 2
OVERRIDE_NrClientsChainB == 2
OVERRIDE_ClientIDsChainA == {"B1", "B2"}
OVERRIDE_ClientIDsChainB == {"A1", "A2"}

=============================================================================
\* Modification History
\* Last modified Wed Oct 07 15:07:25 CEST 2020 by ilinastoilkovska
\* Created Wed Oct 07 15:07:04 CEST 2020 by ilinastoilkovska
