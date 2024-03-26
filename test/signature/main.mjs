import { ethers } from 'ethers'

const abiCoder = ethers.AbiCoder.defaultAbiCoder()
const message = abiCoder.encode(
  ["string"],
  ["Summa"]
)
const hashedMessage = ethers.solidityPackedKeccak256(
  ["bytes"],
  [message]
)

const getSigner = (privKey) => {
  const provider =  new ethers.JsonRpcProvider('http://127.0.0.1:8545')
  return new ethers.Wallet(privKey, provider)
}

// // Account #0
// const privKey = '0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80'
 
// // Account #19
// const privKey = '0xdf57089febbacf7ba0bc227dafbffa9fc08a93fdc68e1e42411a14efcf23656e'

// Account #18
const privKey = "0xde9be858da4a475276426320d5e9262ecfc3ba460bfac56360bfa6c4c28b4ee0";

const signer = getSigner(privKey)

const signature = await signer.signMessage(
  ethers.getBytes(hashedMessage)
)

console.log(signature);
