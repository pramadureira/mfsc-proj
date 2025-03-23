
--===============================================
-- M.EIC037: Formal Methods for Critical Systems
-- 2024/2025
--
-- Mini Project 1
--
-- Group Members:
--   Afonso Osório - 202108700
--   Pedro Angélico - 202108866
--   Sofia Pinto - 202108682
--
--===============================================

enum Status {External, Fresh, Active, Purged}

abstract sig Object {}

sig Message extends Object {
  var status: lone Status
}

sig Mailbox extends Object {
  var messages: set Message  
}

-- Mail application
one sig Mail {
  -- system mailboxes
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  -- user mailboxes
  var uboxes: set Mailbox,

  var op: lone Operator -- added for tracking purposes only
}

-- added for convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent }

------------------------------
-- Frame condition predicates
------------------------------

-- You can use these predicates in the definition of the operators

-- the status of the messages in M is unchanged from a state to the next
pred noStatusChange [M: set Message] {
  all m: M | m.status' = m.status
}

-- the set of messages in each mailbox in MB is unchanged from a state to the next
pred noMessageChange [MB: set Mailbox] {
  all mb: MB | mb.messages' = mb.messages
}

-- the set of user-defined mailboxes is unchanged from a state to the next
pred noUserboxChange {
  Mail.uboxes' = Mail.uboxes
}


------------------
-- Other Predicates
------------------
fun msgMailbox [] : Message -> one Mailbox { ~messages }

pred isFresh [m: Message]  {
	m.status = Fresh
}

pred isActive [m: Message]  {
	m.status = Active
}

pred isExternal [m: Message]  {
	m.status = External
}

pred isPurged [m: Message]  {
	m.status = Purged
}

pred isStatusAfter [m: Message, s: Status] {
	m.status' = s
}

pred existsMailbox [mb: Mailbox]  {
	mb in (Mail.inbox + Mail.drafts + Mail.sent + Mail.trash + Mail.uboxes)
}

-------------
-- Operators
-------------

/* Leave the constraint on Mail.op' in the operators.
   It is there to track the applied operators in each trace  
*/


-- createMessage 
pred createMessage [m: Message] {
  -- Preconditions:
  --   m is not created already
  --   status of m is Fresh
  no m.msgMailbox
  isFresh[m]
 
  -- Postconditions:
  --   status of m' is Active
  --   m is in the drafts mailbox
  isStatusAfter[m, Active]
  after m.msgMailbox = Mail.drafts

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message - m] 
  noMessageChange [Mailbox - Mail.drafts] 
  noUserboxChange

  Mail.op' = CM
}

-- moveMessage
pred moveMessage [m: Message, mb: Mailbox] {
  -- Preconditions:
  --   mb cannot be trash
  --   mb exists in the system
  --   m cannot be already in mb
  --   status of m is Active
  mb != Mail.trash
  existsMailbox [mb]
  m not in mb.messages
  isActive[m]
  
  -- Postconditions:
  --   m' is in mb and no other mailbox
  after m.msgMailbox = mb

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message] 
  noMessageChange [Mailbox - (mb + m.msgMailbox)] 
  noUserboxChange

  Mail.op' = MM
}


-- deleteMessage
pred deleteMessage [m: Message] {
  -- Preconditions:
  --   m cannot be already in trash
  --   status of m is Active
  m.msgMailbox != Mail.trash
  isActive[m]
  
  -- Postconditions:
  --   m' is in trash and no other mailbox
  after m.msgMailbox = Mail.trash

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message] 
  noMessageChange [Mailbox - (Mail.trash + m.msgMailbox)] 
  noUserboxChange

  Mail.op' = DM
}

-- sendMessage
pred sendMessage [m: Message] {
  -- Preconditions:
  --   m is in drafts
  --   status of m is Active
  m.msgMailbox = Mail.drafts
  isActive[m]
  
  -- Postconditions:
  --   m' is in sent and no other mailbox
  after m.msgMailbox = Mail.sent

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message] 
  noMessageChange [Mailbox - (Mail.sent + Mail.drafts)] 
  noUserboxChange

  Mail.op' = SM
}

-- getMessage 
pred getMessage [m: Message] {
  -- Preconditions:
  --   status of m is external
  isExternal[m]
 
  -- Postconditions:
  --   status of m' is active
  --   m' is in inbox and no other mailbox
  isStatusAfter[m, Active]
  after m.msgMailbox = Mail.inbox

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message - m]
  noMessageChange [Mailbox - Mail.inbox] 
  noUserboxChange

  Mail.op' = GM
}


/* Note:
   We assume that the spec implicitly means that the messages are not just
   marked as Purged but are also actually removed from the trash mailbox.
*/
-- emptyTrash
pred emptyTrash {
  -- Preconditions:
  --   trash has messages
  some Mail.trash.messages
  
  -- Postconditions:
  --   status of all messages in trash transitions to purged
  --   trash mailbox is empty
  all m: Mail.trash.messages | after m.status = Purged
  after no Mail.trash.messages

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message - Mail.trash.messages]
  noMessageChange [Mailbox - Mail.trash] 
  noUserboxChange

  Mail.op' = ET
}


-- createMailbox
pred createMailbox [mb: Mailbox] {
  -- Preconditions:
  --   mb is not in the system
  not existsMailbox [mb]

  -- Postconditions:
  --   mb is in uboxes
  Mail.uboxes' = Mail.uboxes + mb

  -- Frame
  --   no changes to the state of other messages,
  --   to the set of messages in the remaining mailboxes, 
  --   or to the user-created mailboxes
  noStatusChange [Message]
  noMessageChange [Mailbox] 


  Mail.op' = CMB
}

-- deleteMailbox
pred deleteMailbox [mb: Mailbox] {
  -- Preconditions:
  -- mb in uboxes
  mb in Mail.uboxes

  -- Postconditions:
  -- all m in mb are purged
  -- mb is removed from the system
  -- all m: mb.messages | m'.status = Purged -- é a mesma coisa?
  after all m: mb.messages | isPurged [m]

  -- Mail.uboxes' = Mail.uboxes - mb -- é a mesma coisa? não
  --after Mail.uboxes = Mail.uboxes - mb
  Mail.uboxes' = Mail.uboxes - mb

  -- Frame
  -- no change to the state of messages not in that mb,
  -- to the set of messages in the remaining mailboxes, 
  noStatusChange [Message - mb.messages]
  noMessageChange [Mailbox - mb]


  Mail.op' = DMB
}

-- noOp
pred noOp {
  noStatusChange [Message] 
  noMessageChange [Mailbox] 
  noUserboxChange
  
  Mail.op' = none 
}

--------------------------
-- Inital state predicate
--------------------------

pred Init {
  -- There exist no active or purged messages anywhere
  no m: Message | isActive [m] or isPurged [m]


  -- The system mailboxes are all distinct
  disj [sent, drafts, inbox, trash]


  -- All mailboxes anywhere are empty
  all mb: Mailbox | no mb.messages


  -- The set of user-created mailboxes is empty
  no Mail.uboxes


  -- [Keep this tracking constraint intact]
  -- no operator generates the initial state
  Mail.op = none
}

------------------------
-- Transition predicate
------------------------

pred Trans {
  (some mb: Mailbox | createMailbox [mb])
  or
  (some mb: Mailbox | deleteMailbox [mb])
  or
  (some m: Message | createMessage [m])
  or  
  (some m: Message | getMessage [m])
  or
  (some m: Message | sendMessage [m])
  or   
  (some m: Message | deleteMessage [m])
  or 
  (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  or 
  emptyTrash
  or 
  noOp
}

----------
-- Traces
----------

-- Restricts the set of traces to all and only the executions of the Mail app

fact System {
  -- traces must satisfy initial state condition and the transition condition
  Init and always Trans
}


--run {} for 10

---------------------
-- Sanity check runs
---------------------

pred p1 {
  -- Eventually a message becomes active
  eventually some m: Message | isActive[m]
}
--run p1 for 1 but 8 Object

pred p2 {
  -- The inbox contains more than one message at some point
  eventually some mb: Mailbox | #mb.messages > 1
}
run p2 for 1 but 8 Object

pred p3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later

}
--run p3 for 1 but 8 Object

pred p4 {
  -- Eventually some message in the drafts mailbox (it is already there) moves to the sent mailbox

}
--run p4 for 1 but 8 Object

pred p5 {
  -- Eventually there is a user mailbox with messages in it

}
--run p5 for 1 but 8 Object 

pred p6 {
  -- Eventually the inbox gets two messages in a row from outside

}
--run p6 for 1 but 8 Object

pred p7 {
  -- Eventually some user mailbox gets deleted

}
run p7 for 1 but 8 Object

pred p8 {
  -- Eventually the inbox has messages

  -- Every message in the inbox at any point is eventually removed 

}
--run p8 for 1 but 8 Object

pred p9 {
  -- The trash mail box is emptied of its messages eventually

}
--run p9 for 1 but 8 Object

pred p10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore

}
--run p10 for 1 but 8 Object



--------------------
-- Valid Properties
--------------------

assert v1 {
--  Every active message is in one of the app's mailboxes 

}
--check v1 for 5 but 11 Object

 
assert v2 {
--  Inactive messages are in no mailboxes at all

}
--check v2 for 5 but 11 Object

assert v3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes

}
--check v3 for 5 but 11 Object

assert v4 {
-- Every active message was once external or fresh.

}
--check v4 for 5 but 11 Object

assert v5 {
-- Every user-created mailbox starts empty.

}
--check v5 for 5 but 11 Object

assert v6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.

}
--check v6 for 5 but 11 Object

assert v7 {
-- Every sent message is sent from the draft mailbox 

}
--check v7 for 5 but 11 Object

assert v8 {
-- The app's mailboxes contain only active messages

}
--check v8 for 5 but 11 Object

assert v9 {
-- Every received message passes through the inbox

}
--check v9 for 5 but 11 Object

assert v10 {
-- A purged message is purged forever

}
--check v10 for 5 but 11 Object

assert v11 {
-- No messages in the system can ever (re)acquire External status

}
--check v11 for 5 but 11 Object

assert v12 {
-- The trash mailbox starts empty and stays so until a message is deleted, if any

}
--check v12 for 5 but 11 Object

assert v13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox it is in.

}
--check v13 for 5 but 11 Object

assert v14 {
-- Every message in the trash mailbox had been previously deleted

}
--check v14 for 5 but 11 Object

assert v15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.

}
--check v15 for 5 but 11 Object

assert v16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted

}
--check v16 for 5 but 11 Object


----------------------
-- Invalid Properties
----------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: 
assert i1 {

}
--check i1 for 5 but 11 Object

-- A message that was removed from the inbox may later reappear there.
-- Negated into:
assert i2 {

}
--check i2 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into:
assert i3 {

}
--check i3 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into:
assert i4 {

}
--check i4 for 5 but 11 Object


