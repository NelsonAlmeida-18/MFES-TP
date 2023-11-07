// Link to challenge: http://alloy4fun.inesctec.pt/M7DaDXS9hn3XkGoZh
sig Bucket {
    var head : lone Node
}
sig Node {
    key : one Key,
    var prox : lone Node
}
sig Key {
    hash : one Hash
}
sig Hash {}



pred check_two[n: Node]{
	//Não existe outro bucket com a mesma hash do nodo que pretendemos inserir
  	//Guard
  	n.key.hash not in Bucket.head.key.hash
  	
  	//Effect
  	//Procuramos um bucket que não tenha nenhum nodo na cabeça( bucket vazio)
  	one b : Bucket | no b.head and (
      	b.head' = n and 
      	all b1 : Bucket-b | b1.head' = b1.head
	)
  	
  	//Frame Condition
  	all n1 : Node | n1.prox' = n1.prox
}
  


pred check_five[n:Node] {
  //Já existe um bucket cujo hash é o mesmo do nodo que pretendemos inserir
  //Guard
  n.key.hash in Bucket.head.key.hash
  
  //Effect
  //Procuramos o bucket cujo hash da head seja igual ao do nodo que pretendemos inserir
  //Verificar se b.head'= n' parece mais correto
  one b:Bucket | b.head.key.hash = n.key.hash and (
    (b.head' = n and n.prox' = b.head) and keepRelations[b,n])
}


fun allNodes[]: set Node {
    { n: Node | n in Bucket.head.*prox }
}

  
pred insert[n : Node] {
  
  	n not in allNodes[]
  
  	check_two[n] or check_five[n]
}

let keepRelations[ b, n] {
  	//This whill keep all the previous connections between nodes before our insertion
 	(all b1: Bucket-b | b1.head' = b1.head) and
	(all n1: Node-n | n1.prox' = n1.prox)
}
