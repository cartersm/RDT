module model/RDT10
open util/ordering[State]

sig State {
	sendBuffer: set Data,
	recvBuffer: set Data
}

sig Data {}

pred State.init {
	all d: Data | d in this.sendBuffer
	no this.recvBuffer
}

pred transition[s, s': State] {
	one d: Data |
		s'.sendBuffer = s.sendBuffer - d and
		s'.recvBuffer = s.recvBuffer + d
}

fact Trace {
	first.init[]
	all s: State - last |
		let s' = s.next |
			transition[s, s']
}

pred finish {
	some s: State | 
		no s.sendBuffer and
		all d: Data | d in s.recvBuffer
}
run finish for 3 State, exactly 2 Data













//abstract sig FSM {}
//
//one sig Sender extends FSM {}
//
//one sig Receiver extends FSM {}
//
//
//
//sig Packet {
//	data: Data
//}
//
//fun make_pkt[d: Data]: Packet {
//	one p: Packet | p.data = d
//}
//
//pred udt_send[p: Packet] {
//	
//}
//
//pred Receiver.rdt_receive[p: Packet] {
//	extract[p]
//}
//
//fun extract[p: Packet]: Data {
//	p.data
//}
