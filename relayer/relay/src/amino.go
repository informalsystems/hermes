package main

import (
	"fmt"
	"io/ioutil"

	"github.com/cosmos/cosmos-sdk/codec"
	codecstd "github.com/cosmos/cosmos-sdk/codec/std"
	"github.com/cosmos/cosmos-sdk/x/auth"
	ibc "github.com/cosmos/cosmos-sdk/x/ibc/07-tendermint/types"
	"github.com/cosmos/gaia/app"
)

// NOTE: this should be run from within the gaia repo, on branch ibc-alpha

func main() {
	b, err := ioutil.ReadFile("signed.json")
	if err != nil {
		panic(err)
	}

	cdc := codecstd.MakeCodec(app.ModuleBasics)

	var stdtx auth.StdTx
	err = cdc.UnmarshalJSON(b, &stdtx)
	if err != nil {
		panic(err)
	}

	msg := stdtx.Msgs[0].(ibc.MsgCreateClient)
	hcv := msg.Header
	header := hcv.SignedHeader.Header
	commit := hcv.SignedHeader.Commit
	vals := hcv.ValidatorSet

	printer(cdc, "header", header)
	printer(cdc, "commit", commit)
	printer(cdc, "vals", vals)
	printer(cdc, "hcv", hcv)
	printer(cdc, "sh", hcv.SignedHeader)
	printer(cdc, "msg", msg)
	printer(cdc, "client", msg.ClientID)
	printer(cdc, "trusting_period", msg.TrustingPeriod)
	printer(cdc, "unbonding_period", msg.UnbondingPeriod)
	printer(cdc, "address", msg.Signer)

}

func printer(cdc *codec.Codec, name string, o interface{}) {
	b, err := cdc.MarshalBinaryBare(o)
	if err != nil {
		panic(err)
	}
	fmt.Printf("%s --------------------------------------------\n", name)
	fmt.Printf("%x\n", b)

}
