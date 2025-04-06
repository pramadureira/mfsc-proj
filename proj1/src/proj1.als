
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

pred existsMailbox [mb: Mailbox]  {
	mb in (sboxes + Mail.uboxes)
}

-------------
-- Operators
-------------

/* Leave the constraint on Mail.op' in the operators.
   It is there to track the applied operators in each trace  
*/

pred genericMove[m: Message, mb: Mailbox] {
	-- Preconditions:
	--   m is active
	--   mb exists in the system
	--   m is not already in mb
	isActive[m]
	existsMailbox[mb]
	m.msgMailbox != mb

	-- Postconditions:
	--   m is removed from its current mailbox
	--   m is added to the desired mailbox
	m.msgMailbox.messages' = m.msgMailbox.messages - m
	mb.messages' = mb.messages + m

	-- No messages change status
	-- Only the source and destination mailboxes are altered
	-- No mailboxes are added or removed
	noStatusChange[Message]
	noMessageChange[Mailbox - (mb + m.msgMailbox)]
	noUserboxChange
}


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
  after isActive[m]
  --after m.msgMailbox = Mail.drafts
  Mail.drafts.messages' = Mail.drafts.messages + m

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
  mb != Mail.trash
  -- TODO: Confirm -> added because of assert v7 and v9
  mb != Mail.sent
  mb != Mail.inbox
  
  genericMove[m, mb]

  Mail.op' = MM
}


-- deleteMessage
pred deleteMessage [m: Message] {
  -- Preconditions:
  --   m cannot be already in trash
  m.msgMailbox != Mail.trash
  
  -- Postconditions:
  genericMove[m, Mail.trash]

  Mail.op' = DM
}

-- sendMessage
pred sendMessage [m: Message] {
  -- Preconditions:
  --   m is in drafts
  m.msgMailbox = Mail.drafts
  
  -- Postconditions:
  genericMove[m, Mail.sent]

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
  after isActive[m]
  --after m.msgMailbox = Mail.inbox
  Mail.inbox.messages' = Mail.inbox.messages + m

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
   all m: mb.messages | after isPurged [m]
   mb.messages' = none

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
--run p2 for 1 but 8 Object

pred p3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later
  eventually (some Mail.trash.messages and eventually Mail.op = ET)
}
--run p3 for 1 but 8 Object

pred p4 {
  -- Eventually some message in the drafts mailbox (it is already there) moves to the sent mailbox
  eventually (some m: Mail.drafts.messages | eventually m in Mail.sent.messages)
}
--run p4 for 1 but 8 Object

pred p5 {
  -- Eventually there is a user mailbox with messages in it
  eventually some Mail.uboxes.messages
}
--run p5 for 1 but 8 Object 

pred p6 {
  -- Eventually the inbox gets two messages in a row from outside
  eventually some m1, m2: Message | let mbMsgs = Mail.inbox.messages |
    isExternal[m1] and isExternal[m2] and m1 != m2 and
    (eventually (mbMsgs =  mbMsgs + m1 and after mbMsgs =  mbMsgs + m2))
}
--run p6 for 1 but 8 Object

pred p7 {
  -- Eventually some user mailbox gets deleted
  eventually (some u: Mail.uboxes | eventually Mail.uboxes = Mail.uboxes - u)
}
--run p7 for 1 but 8 Object


pred p8 {
  -- Eventually the inbox has messages
  eventually some Mail.inbox.messages
  -- Every message in the inbox at any point is eventually removed
  always all m: Mail.inbox.messages | eventually m not in Mail.inbox.messages
}
--run p8 for 1 but 8 Object


pred p9 {
  -- The trash mail box is emptied of its messages eventually
  eventually (some Mail.trash.messages and eventually no Mail.trash.messages)
}
--run p9 for 1 but 8 Object

pred p10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore
  eventually (one m: Message | isExternal[m])
  after always noOp
}
--run p10 for 1 but 8 Object



--------------------
-- Valid Properties
--------------------

assert v1 {
  --  Every active message is in one of the app's mailboxes 
  always all m: Message | isActive[m] => m in (sboxes.messages + Mail.uboxes.messages)
}
--check v1 for 5 but 11 Object


assert v2 {
--  Inactive messages are in no mailboxes at all
	--always all m: status.(Status - Active) | m.msgMailbox = none
	always no status.(Status - Active) & Mailbox.messages
}
--check v2 for 5 but 11 Object

assert v3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes
  always no Mail.uboxes & sboxes
}
--check v3 for 5 but 11 Object

assert v4 {
-- Every active message was once external or fresh.
  always all m: Message | isActive[m] => once (isExternal[m] or isFresh[m])
}
--check v4 for 5 but 11 Object

assert v5 {
-- Every user-created mailbox starts empty.
  always all ub: Mail.uboxes | (before ub not in Mail.uboxes) => no ub.messages

}
--check v5 for 5 but 11 Object

assert v6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.
  always all ub: Mail.uboxes | (deleteMailbox[ub]) releases (ub in Mail.uboxes)
}
--check v6 for 5 but 11 Object

assert v7 {
-- Every sent message is sent from the draft mailbox 
  always all m: Message | sendMessage[m] => m in Mail.drafts.messages
}
--check v7 for 5 but 11 Object

assert v8 {
-- The app's mailboxes contain only active messages
  always all m: (sboxes.messages + Mail.uboxes.messages) | isActive[m]
}
--check v8 for 5 but 11 Object

assert v9 {
-- Every received message passes through the inbox
  always all m: Message | getMessage[m] => m in Mail.inbox.messages'
}
--check v9 for 5 but 11 Object

assert v10 {
-- A purged message is purged forever
  always all m: Message |  isPurged[m] => always isPurged[m]
}
--check v10 for 5 but 11 Object

assert v11 {
-- No messages in the system can ever (re)acquire External status
  always all m:Message |  not isExternal[m] => always not isExternal[m]
}
--check v11 for 5 but 11 Object

assert v12 {
-- The trash mailbox starts empty and stays so until a message is deleted, if any
    (after Mail.op = DM) releases (no Mail.trash.messages)
}
--check v12 for 5 but 11 Object

assert v13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox it is in.
  --always all m: Message | isPurged[m] => (once Message = Message - m) or (no messages.m & (sboxes + Mail.uboxes))
  always all m: Message | (isPurged[m] and before isActive[m]) => (once deleteMessage[m]) or (before deleteMailbox[m.msgMailbox])
}
--check v13 for 5 but 11 Object

assert v14 {
-- Every message in the trash mailbox had been previously deleted
  /*always all m: Mail.trash.messages |
    once ((Mail.trash.messages = Mail.trash.messages - m) and
    (m in (sboxes.messages + Mail.uboxes.messages)))*/
  always all m: Mail.trash.messages | (before m in Mail.trash.messages) or (once deleteMessage[m])
}
--check v14 for 5 but 11 Object

assert v15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.
    always all m: Mail.uboxes.messages | once m in sboxes.messages
}
--check v15 for 5 but 11 Object

assert v16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted
  /*always all m: Message | (((isPurged[m]) and (historically m not in Mail.trash.messages)) => 
  ((once m in Mail.uboxes.messages) => (eventually Mail.uboxes = Mail.uboxes - messages.m)))*/
  always all m: status.Purged | (historically m not in Mail.trash.messages) => once (m.msgMailbox in Mail.uboxes and deleteMailbox[m.msgMailbox])
}
--check v16 for 5 but 11 Object


----------------------
-- Invalid Properties
----------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: 
assert i1 {
  -- There is no message that is always in the inbox
  always (no m: status.Active | always m in Mail.inbox.messages)
}
--check i1 for 5 but 11 Object

-- A message that was removed from the inbox may later reappear there.
-- Negated into:
-- TODO: currently doesnt work because of changes to moveMessage
assert i2 {
  --no m: Message | eventually ((m in Mail.inbox.messages and deleteMessage[m]) and after eventually m in Mail.inbox.messages) 
  no m: Message | eventually (m in Mail.inbox.messages and eventually (m not in Mail.inbox.messages and eventually (m in Mail.inbox.messages)))
}
--check i2 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into:
-- TODO: verify this one more closely
assert i3 {
  -- If a message is deleted, it never goes back to the mailbox it was deleted from.
  all m: Message | (eventually m in Mail.trash.messages) => (always m not in messages.m.messages)
}
--check i3 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into:
assert i4 {
  -- All external messages will eventually be received
  all m: Message | isExternal[m] => eventually m in Mail.inbox.messages
}
--check i4 for 5 but 11 Object


