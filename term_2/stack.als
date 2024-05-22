open util/ordering[State] as ord

module stack

enum Action {
	POP,
	PUSH,
	STUTTER
}

sig State{
	var s: one Stack,
	var act: Action,
	var deleted: set Node
}

one sig Stack { 
	var root: lone Node
}

sig Node {
	next: lone Node
}

fun first_elem  : one Node { Stack.root }

fact noDeleted {
	no n:Node | n in State.deleted and n in State.s.root.*next
}

fact nextNotSelf {
	no n:Node | n = n.next
}

fact allNodesBelong {
	all n:Node | one s:Stack | n in s.root.*next
}

fact nextNotCyclic {
	no n:Node | n in n.^next
}

pred stutter(){
	State'.act = STUTTER
	State'.s = State.s 
	State'.deleted = State.deleted
}

pred push[new : Node]{
	State.act' = PUSH
	first_elem' = new
	first_elem'.next' = first_elem
}

pred pop{
	some i: Node | i in State.s.root.*next

	State'.deleted = State.deleted + State.s.root
	
	State'.s.root = State.s.root.next
}

pred transition {
	stutter or (some i: Node | push[i]) or 
	pop
}

pred show() {}

// get sample instances
run {always transition} for 5
