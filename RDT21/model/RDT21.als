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
	feedback: lone Packet,
	sentData: lone Data,
	channelSequence: one SequenceNum,
	expectedSequence: one SequenceNum
}

sig Data {}

sig Checksum {
	data: one Data
}

sig SequenceNum {
}

sig BadData extends Data {}

sig Packet {}

one sig ACK, NAK, BadACKNAK extends Packet {}

pred State.init {
	all d: Data - BadData | d in this.sendBuffer
	no d: BadData | d in this.sendBuffer
	no this.recvBuffer
	no this.channel
	no this.channelChecksum
	this.feedback = ACK
	no this.sentData
	this.channelSequence != this.expectedSequence
}

pred transition[s, s': State] {
	//If something in the channel
	one s.channel => (
		//If checksum matches data
		s.channelChecksum.data = extract[s] =>
		(
			s.channelSequence = s.expectedSequence =>
			(
				s'.recvBuffer = s.recvBuffer + extract[s] and
				s'.sendBuffer = s.sendBuffer and
				no s'.channel and
				no s'.channelChecksum and
				(s'.feedback = ACK or s'.feedback = BadACKNAK) and
				s'.sentData = s.sentData and
				s'.channelSequence = s.channelSequence and
				s'.expectedSequence != s.expectedSequence
			) else (
				s'.recvBuffer = s.recvBuffer and
				s'.sendBuffer = s.sendBuffer and
				no s'.channel and
				no s'.channelChecksum and
				(s'.feedback = ACK or s'.feedback = BadACKNAK) and
				s'.sentData = s.sentData and
				s'.channelSequence = s.channelSequence and
				s'.expectedSequence = s.expectedSequence
			)
		) else (
			s'.recvBuffer = s.recvBuffer and
			s'.sendBuffer = s.sendBuffer and
			no s'.channel and
			no s'.channelChecksum and
			(s'.feedback = NAK or s'.feedback = BadACKNAK) and
			s'.sentData = s.sentData and
			s'.channelSequence = s.channelSequence and
			s'.expectedSequence = s.expectedSequence
		)
	)
	//if there's nothing in the channel and feedback is ACK
	else s.feedback = ACK => (
		//There is either another data to send
		(one d: Data - BadData |
			not d in s.recvBuffer and
			s'.sendBuffer = s.sendBuffer - d and
			s'.recvBuffer = s.recvBuffer and
			make_pkt[s', d] and
			no s'.feedback and
			s'.sentData = d and
			s'.channelSequence != s.channelSequence and
			s'.expectedSequence = s.expectedSequence) or
		//There is no more data to send
		(
			(no d: Data - BadData | d in s.sendBuffer) and
			no s'.sentData and
			s'.sendBuffer = s.sendBuffer and
			s'.recvBuffer = s.recvBuffer and
			no s'.feedback and
			no s'.channel and
			s'.channelSequence = s.channelSequence and
			s'.expectedSequence = s.expectedSequence
		)
	) else s.feedback = NAK => (
		s'.sendBuffer = s.sendBuffer and
		s'.recvBuffer = s.recvBuffer and
		make_pkt[s', s.sentData] and
		no s'.feedback and
		s'.sentData = s.sentData and
		s'.channelSequence = s.channelSequence and
		s'.expectedSequence = s.expectedSequence
	) else s.feedback = BadACKNAK => (
		s'.sendBuffer = s.sendBuffer and
		s'.recvBuffer = s.recvBuffer and
		make_pkt[s', s.sentData] and
		no s'.feedback and
		s'.sentData = s.sentData and
		s'.channelSequence = s.channelSequence and
		s'.expectedSequence = s.expectedSequence
	)
}

fact Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			(not s.finished and transition[s, s']) or
			(s.finished and s'.finished and
			 no s'.sentData and
			 s.channelSequence = s'.channelSequence and
			 s.expectedSequence = s'.expectedSequence and
			 no s'.feedback)		
}

pred State.finished {
	no this.sendBuffer and
	no this.channel and
	no this.channelChecksum and
	(all d: Data - BadData | d in this.recvBuffer) and
	no this.sentData
}

pred make_pkt[s: State, d: Data] {
	one p: Packet |
	(
		(	
			s.channel = p->d or
			one b: BadData | s.channel = p->b
		) and
		one c: Checksum | (
			c.data = d and
			s.channelChecksum = c
		)
	)
}

fun extract[s: State]: Data {
	s.channel[Packet]
}

fact DisjointChecksums {
	all disj c, c': Checksum | not c.data = c'.data
	all c: Checksum | not c.data in BadData
}

fact NoAckNakInChannel {
	all s: State |
		(all d: Data |
			not ACK -> d in s.channel and
			not NAK -> d in s.channel and
			not BadACKNAK -> d in s.channel
		) and
		(
			s.feedback = ACK or
			s.feedback = NAK or
			s.feedback = BadACKNAK or
			no s.feedback
		)
}

fact NoBadDataInRecvBuffer {
	all s: State | no d: BadData | d in s.recvBuffer
}

pred finish {
	some s: State | 
		s.finished
}
run finish for 8 State, exactly 3 Data, exactly 1 BadData, exactly 2 Checksum, 4 Packet, exactly 2 SequenceNum

assert allFinish {
	some s: State |
		s.finished
}
check allFinish for 8 State, exactly 3 Data, exactly 1 BadData, exactly 2 Checksum, 4 Packet, exactly 2 SequenceNum

assert allFinishLoneError {
	(some s: State | s.finished) and
	(lone s: State | (s.feedback in BadACKNAK or s.feedback in NAK)) => (some s: State | s.finished)
}

check allFinishLoneError for 8 State, exactly 3 Data, exactly 1 BadData, exactly 2 Checksum, 4 Packet, exactly 2 SequenceNum


