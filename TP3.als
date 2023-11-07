//Link to challenge: http://alloy4fun.inesctec.pt/MzMDN92qAyeaMcGoC
sig Bucket {
	head : lone Node
}

sig Node {
	key : one Key,
	prox : lone Node
}

sig Key {
	hash : one Hash
}

sig Hash {}

pred Invs {
	// Specify the properties that characterize 
	// hash tables using closed addressing (separate 
	// chaining) for collision resolution.

	// The points you will get is proportional to the 
	// number of correct properties. To check how many
	// points you have so far you can use the different
 	// commands. For example, if check Three is correct 
	// you will have at least 3 points.
    // The maximum is 5 points.

	// Be careful to not overspecify! 
	// If you specify a property that is not valid in 
	// these hash tables you get 0 points, 
    // even if you have some correct properties.
	// To check if you are not overspecifying you can use 
	// command NoOverspecification. If you have an invalid
	// property this command will return a valid hash table 
	// that you specification is not accepting.
  
  	//Every hash is associated to a node
  	all k:Key | one n : Node | n.key=k
  
  	//Every node is associated with a bucket
  	all n : Node | some b : Bucket | n in NodesInBucket[b]
  
    //For all nodes in a bucket, they must have the same hash value
  
  								// the bucket is empty 	
  								//or has one element
	  all b: Bucket ,n: NodesInBucket[b] | lone n implies b.head.key.hash = n.key.hash

  
  	//Every bucket has a unique hash key
  	all disj b,b1 :Bucket | (no b.head or no b1.head) or (b.head.key.hash!=b1.head.key.hash)

	//Every node has a next node diferent than itself
	//all b:Bucket, k:Key| b.head	
  //all b : Bucket , n,n1: NodesInBucket[b] | ( no b.head ) or (no b.head.prox) or n.prox in n1-n
	
	//For every bucket, there isnt a cycle with its nodes
	all b: Bucket |
  no n: NodesInBucket[b] | n in n.^prox
	
}

fun NodesInBucket[b: Bucket]: set Node {
    { n: Node | n in b.head.*prox }
}
