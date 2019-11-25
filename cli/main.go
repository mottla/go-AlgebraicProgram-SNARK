package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"github.com/urfave/cli"
	"io/ioutil"
	"log"
	"math/big"
	"os"
)

func panicErr(err error) {
	if err != nil {
		panic(err)
	}
}

//TODO EVERYTHING This class is unfinished. See wolf19_test at this point
var commands = []cli.Command{
	{
		Name:    "compile",
		Aliases: []string{},
		Usage:   "compile a circuit",
		Action:  CompileCircuit,
	},
	{
		Name:    "trustedsetup",
		Aliases: []string{},
		Usage:   "generate trusted setup for a circuit",
		Action:  TrustedSetup,
	},
	{
		Name:    "genproofs",
		Aliases: []string{},
		Usage:   "generate the snark proofs",
		Action:  GenerateProofs,
	},
	{
		Name:    "verify",
		Aliases: []string{},
		Usage:   "verify the snark proofs",
		Action:  VerifyProofs,
	},
}

func main() {
	app := cli.NewApp()
	app.Name = "go-snarks-cli"
	app.Version = "0.0.1-alpha"
	app.Flags = []cli.Flag{
		cli.StringFlag{Name: "config"},
	}
	app.Commands = commands

	err := app.Run(os.Args)
	if err != nil {
		log.Fatal(err)
	}
}

func CompileCircuit(context *cli.Context) error {
	fmt.Println("cli")

	circuitPath := context.Args().Get(0)

	// read circuit file
	circuitFile, err := os.Open(circuitPath)
	panicErr(err)

	// parse circuit code
	parser := circuitcompiler.NewParser(bufio.NewReader(circuitFile))

	jsonFile, err := os.Create("compiledcircuit.json")
	panicErr(err)
	defer jsonFile.Close()
	jsonFile.Write(jsonData)
	jsonFile.Close()
	fmt.Println("Compiled Circuit data written to ", jsonFile.Name())

	return nil
}

func TrustedSetup(context *cli.Context) error {
	// open compiledcircuit.json
	compiledcircuitFile, err := ioutil.ReadFile("compiledcircuit.json")
	panicErr(err)
	var circuit circuitcompiler.Circuit
	json.Unmarshal([]byte(string(compiledcircuitFile)), &circuit)
	panicErr(err)

	// read privateInputs file
	privateInputsFile, err := ioutil.ReadFile("privateInputs.json")
	panicErr(err)
	// read publicInputs file
	publicInputsFile, err := ioutil.ReadFile("publicInputs.json")
	panicErr(err)

	// parse inputs from inputsFile
	var inputs circuitcompiler.Inputs
	err = json.Unmarshal([]byte(string(privateInputsFile)), &inputs.Private)
	panicErr(err)
	err = json.Unmarshal([]byte(string(publicInputsFile)), &inputs.Public)
	panicErr(err)

	// calculate wittness

	// ER1CS to QAP

	// calculate trusted setup

	// remove setup.Toxic

	// store setup to json
	jsonData, err := json.Marshal(tsetup)
	panicErr(err)
	// store setup into file
	jsonFile, err := os.Create("trustedsetup.json")
	panicErr(err)
	defer jsonFile.Close()
	jsonFile.Write(jsonData)
	jsonFile.Close()
	fmt.Println("Trusted Setup data written to ", jsonFile.Name())
	return nil
}

func GenerateProofs(context *cli.Context) error {
	// open compiledcircuit.json
	compiledcircuitFile, err := ioutil.ReadFile("compiledcircuit.json")
	panicErr(err)
	var circuit circuitcompiler.Circuit
	json.Unmarshal([]byte(string(compiledcircuitFile)), &circuit)
	panicErr(err)

	// open trustedsetup.json
	trustedsetupFile, err := ioutil.ReadFile("trustedsetup.json")
	panicErr(err)
	//var trustedsetup snark.Setup
	//json.Unmarshal([]byte(string(trustedsetupFile)), &trustedsetup)
	panicErr(err)

	// read privateInputs file
	privateInputsFile, err := ioutil.ReadFile("privateInputs.json")
	panicErr(err)
	// read publicInputs file
	publicInputsFile, err := ioutil.ReadFile("publicInputs.json")
	panicErr(err)
	// parse inputs from inputsFile
	var inputs circuitcompiler.Inputs
	err = json.Unmarshal([]byte(string(privateInputsFile)), &inputs.Private)
	panicErr(err)
	err = json.Unmarshal([]byte(string(publicInputsFile)), &inputs.Public)
	panicErr(err)

	// calculate wittness
	w, err := circuit.CalculateWitness(inputs.Private, inputs.Public)
	panicErr(err)
	fmt.Println("witness", w)

	// flat code to ER1CS

	// ER1CS to QAP

	// store proofs to json
	jsonData, err := json.Marshal(proof)
	panicErr(err)
	// store proof into file
	jsonFile, err := os.Create("proofs.json")
	panicErr(err)
	defer jsonFile.Close()
	jsonFile.Write(jsonData)
	jsonFile.Close()
	fmt.Println("Proofs data written to ", jsonFile.Name())
	return nil
}

func VerifyProofs(context *cli.Context) error {
	// open proofs.json
	proofsFile, err := ioutil.ReadFile("proofs.json")
	panicErr(err)
	//var proof snark.Proof
	//json.Unmarshal([]byte(string(proofsFile)), &proof)
	panicErr(err)

	// open compiledcircuit.json
	compiledcircuitFile, err := ioutil.ReadFile("compiledcircuit.json")
	panicErr(err)
	var circuit circuitcompiler.Circuit
	json.Unmarshal([]byte(string(compiledcircuitFile)), &circuit)
	panicErr(err)

	// open trustedsetup.json
	trustedsetupFile, err := ioutil.ReadFile("trustedsetup.json")
	panicErr(err)
	//var trustedsetup snark.Setup
	//json.Unmarshal([]byte(string(trustedsetupFile)), &trustedsetup)
	panicErr(err)

	// read publicInputs file
	publicInputsFile, err := ioutil.ReadFile("publicInputs.json")
	panicErr(err)
	var publicSignals []*big.Int
	err = json.Unmarshal([]byte(string(publicInputsFile)), &publicSignals)
	panicErr(err)

	//verified := snark.VerifyProof(circuit, trustedsetup, proof, publicSignals, true)
	//if !verified {
	//	fmt.Println("ERROR: proofs not verified")
	//} else {
	//	fmt.Println("Proofs verified")
	//}
	return nil
}
