module model/RDT10
open util/ordering[State]

/*
 * Authors: "The Awesome Team"
 * 		Sean Carter
 * 		Austin Willis
 */

sig State {
	sendBuffer: set Data,
	recvBuffer: set Data,
	channel: Packet->Data
}

sig Data {}

sig Packet {}

pred State.init {
	all d: Data | d in this.sendBuffer
	no this.recvBuffer
	no this.channel
}

pred transition[s, s': State] {
	one s.channel => (
		s'.recvBuffer = s.recvBuffer + extract[s] and
		s'.sendBuffer = s.sendBuffer and
		no s'.channel
	)
	else (one d: Data |
		not d in s.recvBuffer and
		s'.sendBuffer = s.sendBuffer - d and
		s'.recvBuffer = s.recvBuffer and
		make_pkt[s', d]
	)
}

fact Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			transition[s, s']
}

pred make_pkt[s: State, d: Data] {
	one p: Packet | s.channel = p->d
}

fun extract[s: State]: Data {
	s.channel[Packet]
}

pred finish {
	some s: State | 
		no s.sendBuffer and
		no s.channel and
		all d: Data | d in s.recvBuffer
}
run finish for 5 State, exactly 2 Data, 1 Packet

assert allFinish {
	one s: State |
		no s.sendBuffer and
		no s.channel and
		all d: Data | d in s.recvBuffer
}
check allFinish for 5 State, exactly 2 Data, 1 Packet













