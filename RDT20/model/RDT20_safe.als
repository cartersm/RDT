module model/RDT20
open util/ordering[State]

/*
 * Authors: "The Awesome Team"
 * 		Sean Carter
 * 		Austin Willis
 */

sig State {
	sendBuffer: set Data,
	recvBuffer: set Data,
	channel: Packet->Data,
	channelChecksum: lone Checksum,
	feedback: lone Packet
}

sig Data {}

sig Checksum {
	data: one Data
}

sig BadData extends Data {}

sig Packet {}

one sig ACK, NAK extends Packet {}

pred State.init {
	all d: Data - BadData | d in this.sendBuffer
	no d: BadData | d in this.sendBuffer
	no this.recvBuffer
	no this.channel
	no this.channelChecksum
	this.feedback = ACK
}

pred transition[s, s': State] {
	//If something in the channel
	one s.channel => (
		//If checksum matches data
		s.channelChecksum.data = extract[s] =>
		(
			s'.recvBuffer = s.recvBuffer + extract[s] and
			s'.sendBuffer = s.sendBuffer and
			no s'.channel and
			no s'.channelChecksum and
			s'.feedback = ACK
		)
	)
	//if there's nothing in the channel and feedback is ACK
	else s.feedback = ACK => (
		one d: Data - BadData |
			not d in s.recvBuffer and
			s'.sendBuffer = s.sendBuffer - d and
			s'.recvBuffer = s.recvBuffer and
			make_pkt[s', d] and
			no s'.feedback
	)
}

fact Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			(not s.finished and transition[s, s']) or
			(s.finished	and s'.finished)		
}

pred State.finished {
	no this.sendBuffer and
	no this.channel and
	no this.channelChecksum and
	all d: Data - BadData | d in this.recvBuffer
}

pred make_pkt[s: State, d: Data] {
	one p: Packet |
	(
		s.channel = p->d and
		one c: Checksum | (
			c.data = d and
			s.channelChecksum = c
		)
	)
}

fun extract[s: State]: Data {
	s.channel[Packet]
}

fact {
	all disj c, c': Checksum | not c.data = c'.data
	all c: Checksum | not c.data in BadData
}

fact {
	all s: State |
		(all d: Data |
			not ACK -> d in s.channel and
			not NAK -> d in s.channel
		) and
		(
			s.feedback = ACK or
			s.feedback = NAK or
			no s.feedback
		)
}

fact {
	all s: State | no d: BadData | d in s.recvBuffer
}

pred finish {
	some s: State | 
		s.finished
}
run finish for 7 State, exactly 3 Data, exactly 1 BadData, exactly 2 Checksum, 3 Packet

assert allFinish {
	some s: State |
		s.finished
}
check allFinish for 7 State, exactly 3 Data, exactly 1 BadData, exactly 2 Checksum, 3 Packet




