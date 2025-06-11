/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
  Afonso Osório - 202108700
  Pedro Madureira - 202108866
  Sofia Pinto - 202108682
  ===============================================*/

include "List.dfy"

import opened L = List
  
// The next three classes have a minimal class definition,
// for simplicity
class Address 
{
  constructor () {}
}

class Date 
{
  constructor () {}
}

class MessageId 
{
  constructor () {}
}

//==========================================================
//  Message
//==========================================================
class Message
{
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: seq<Address>

  constructor (s: Address)
    ensures fresh(id)
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == []
  {
    sender := s;
    content := "";
    recipients := [];
    date := new Date();
    id := new MessageId();
  }

  method setContent(c: string)
    modifies this
    ensures content == c
    ensures {id, date, sender} == old({id, date, sender})
    ensures recipients == old(recipients)
  {
    content := c;
  }
  
  method setDate(d: Date)
    modifies this
    ensures date == d
    ensures {id, sender} == old({id, sender})
    ensures recipients == old(recipients)
    ensures content == old(content)
  {
    date := d;
  }
 
 
  method addRecipient(p: nat, r: Address)
    modifies this
    requires p <= |recipients|
    ensures |recipients| == |old(recipients)| + 1
    ensures forall i :: 0 <= i < p ==> recipients[i] == old(recipients[i])
    ensures recipients[p] == r
    ensures forall i :: p < i < |recipients| ==> recipients[i] == old(recipients[i-1])
    ensures {id, date, sender} == old({id, date, sender})
    ensures content == old(content)
  {
    recipients := recipients[..p] + [r] + recipients[p..];
  }
}

//==========================================================
//  Mailbox
//==========================================================
//
// Each Mailbox has a name, which is a string. 
// Its main content is a set of messages.
//
class Mailbox { //Add specifications to the following
  var name: string
  var messages: set<Message>
 
  // Creates an empty mailbox with name n
  constructor (n: string)
    ensures name == n
    ensures messages == {}
  {
    name := n;
    messages := {};
  }

  // Adds message m to the mailbox
  method add(m: Message)
    modifies this
    requires m !in messages                   // Ensures that we will not add a repeated message to the same mailbox
    ensures messages == old(messages) + {m}   // The only change to messages is the addition of m
    ensures name == old(name)                 // Mailbox's name remains the same
  {    
    messages := messages + { m };
  }

  // Removes message m from mailbox
  // m need not be in the mailbox 
  method remove(m: Message)
    modifies this
    ensures messages == old(messages) - {m}   // The only change to messages is the removal of m
    ensures name == old(name)                 // Mailbox's name remains the same
  {
    messages := messages - { m };
  }

  // Empties the mailbox
  method empty()
    modifies this
    requires messages != {}       // Ensures that we will not try to empty an already empty mailbox
    ensures messages == {}        // The Mailbox will now be empty of messages
    ensures name == old(name)     // Mailbox's name remains the same
  {
    messages := {};
  }
}

//==========================================================
//  MailApp
//==========================================================
class MailApp {
  // abstract field for user defined boxes
  ghost var userBoxes: set<Mailbox>
  
  // abstract function returning all system mailboxes in one set
  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent} }

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  // userboxList implements userBoxes 
  var userboxList: List<Mailbox>

  // Class invariant
  ghost predicate isValid()
  reads this
  {
    // replace each `true` by your formulation of the invariants 
    // described below
    //----------------------------------------------------------
    // Abstract state invariants
    //----------------------------------------------------------
    // 1. all system mailboxes (inbox, ..., sent) are distinct
    && |systemBoxes()| == 4

    // 2. none of the system mailboxes are in the set
    //    of user-defined mailboxes
    && systemBoxes() * userBoxes == {}
      
    //----------------------------------------------------------
    // Abstract-to-concrete state invariants
    //----------------------------------------------------------
    // userBoxes is the set of mailboxes in userboxList
    && userBoxes == elements(userboxList)
  }

  constructor ()
  ensures isValid()
  ensures fresh(inbox) && inbox.name == "Inbox" && inbox.messages == {}     // Ensures inbox has just been created with no messages and named "Inbox"
  ensures fresh(drafts) && drafts.name == "Drafts" && drafts.messages == {} // Ensures drafts has just been created with no messages and named "Drafts"
  ensures fresh(trash) && trash.name == "Trash" && trash.messages == {}     // Ensures trash has just been created with no messages and named "Trash"
  ensures fresh(sent) && sent.name == "Sent" && sent.messages == {}         // Ensures sent has just been created with no messages and named "Sent"
  ensures userBoxes == {}                                                   // Ensures there are no user boxes

  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    userboxList := Nil;

    userBoxes := {};
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
  modifies this

  requires isValid()
  requires mb in userBoxes                      // Ensures that we will only try to delete a mailbox that actually exists in userBoxes

  ensures userBoxes == old(userBoxes) - {mb}    // The only change to userBoxes is the removal of mb
  ensures inbox == old(inbox)                   // inbox remains the same
  ensures drafts == old(drafts)                 // drafts remains the same
  ensures sent == old(sent)                     // sent remains the same
  ensures trash == old(trash)                   // trash remains the same
  ensures isValid()
  {
    userboxList := remove(userboxList, mb);

    userBoxes := userBoxes - {mb};
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
  modifies this

  requires isValid()
  requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n       // There is no mailbox in userBoxes called n

  ensures exists mb: Mailbox :: fresh(mb) &&                            // mb has just been created
                                mb.name == n &&                         // mb is called n
                                userBoxes == old(userBoxes) + {mb} &&   // The only new mailbox in userBoxes is mb
                                mb.messages == {}                       // mb has no messages in it
  ensures inbox == old(inbox)                                           // inbox remains the same
  ensures drafts == old(drafts)                                         // drafts remains the same
  ensures sent == old(sent)                                             // sent remains the same
  ensures trash == old(trash)                                           // trash remains the same
  ensures isValid()
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);

    userBoxes := userBoxes + {mb};
  }


  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
  modifies drafts

  requires isValid()

  ensures exists m: Message :: fresh(m) &&                                        // m has just been created
                               drafts.messages == old(drafts.messages) + {m} &&   // the only message added to drafts was m
                               m.sender == s                                      // s is the sender of m
  ensures drafts.name == old(drafts.name)                                         // drafts name remains the same
  ensures isValid()
  {
    var m := new Message(s);
    drafts.add(m);
  }


  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
  modifies mb1, mb2
  requires isValid()
  requires m in mb1.messages                       // m must be in mb1, in order to be removed
  requires m !in mb2.messages                      // m must not be in mb2, in order to be added to it
  requires mb1 != mb2                              // mb1 and mb2 must be different

  ensures mb1.messages == old(mb1.messages) - {m}  // m is removed from mb1
  ensures mb2.messages == old(mb2.messages) + {m}  // m is added to mb2
  ensures mb1.name == old(mb1.name)                // name of mb1 remains the same
  ensures mb2.name == old(mb2.name)                // name of mb2 remains the same
  ensures isValid()
  {
    mb1.remove(m);
    mb2.add(m);
  }

  // Moves message m from non-null mailbox mb to the trash mailbox
  // provided that mb is not the trash mailbox
  method deleteMessage (m: Message, mb: Mailbox)
  modifies mb, trash
  requires isValid()
  requires m in mb.messages                            // m must be in mb, in order to be removed
  requires m !in trash.messages                        // m must not be in trash, in order to be added to it
  requires mb != trash                                 // mb must not be trash

  ensures mb.messages == old(mb.messages) - {m}        // m is removed from mb
  ensures trash.messages == old(trash.messages) + {m}  // m is added to trash
  ensures mb.name == old(mb.name)                      // name of mb remains the same
  ensures trash.name == old(trash.name)                // name of trash remains the same
  ensures isValid()
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
  modifies drafts, sent
  requires isValid()
  requires m in drafts.messages                          // m must be in drafts, in order to be removed
  requires m !in sent.messages                           // m must not be in sent, in order to be added to it
  requires drafts != sent                                // drafts and sent must be different
  requires m.recipients != []                            // A message can't be sent if it doesn't have receipients

  ensures drafts.messages == old(drafts.messages) - {m}  // m is removed from drafts
  ensures sent.messages == old(sent.messages) + {m}      // m is added to sent
  ensures drafts.name == old(drafts.name)                // name of drafts remains the same
  ensures sent.name == old(sent.name)                    // name of sent remains the same
  ensures isValid()

  {
    moveMessage(m, drafts, sent);
  }

  // Empties the trash mailbox
  method emptyTrash ()
  modifies trash
  requires isValid()
  requires trash.messages != {}           // Ensures that we are not emptying an empty trash
  ensures trash.messages == {}            // trash is now empty of messages
  ensures trash.name == old(trash.name)   // trash name remains the same
  ensures isValid()
  {
    trash.empty();
  }
}


// Test
/* Can be used to test your code. */

method test() {

  var ma := new MailApp(); 
  assert ma.inbox.name == "Inbox";
  assert ma.drafts.name == "Drafts";
  assert ma.trash.name == "Trash";
  assert ma.sent.name == "Sent";
  assert ma.inbox.messages == ma.drafts.messages ==
                              ma.trash.messages ==
                              ma.sent.messages == {};

  ma.newMailbox("students"); 
  assert exists mb: Mailbox :: mb in ma.userBoxes &&
                               mb.name == "students" &&
                               mb.messages == {};

  var s := new Address();
  ma.newMessage(s);        
  assert exists nw: Message :: ma.drafts.messages == {nw};
}

