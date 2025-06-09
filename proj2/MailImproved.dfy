/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
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
    requires p < |recipients|
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
    requires m !in messages // Ensures that we will not add a repeated message to the same mailbox
    ensures messages == old(messages) + {m}
    ensures name == old(name)
  {    
    messages := messages + { m };
  }

  // Removes message m from mailbox
  // m need not be in the mailbox 
  method remove(m: Message)
    modifies this
    ensures messages == old(messages) - {m}
    ensures name == old(name)
  {
    messages := messages - { m };
  }

  // Empties the mailbox
  method empty()
    modifies this
    requires messages != {} // Ensures that we will not try to empty an already empty mailbox
    ensures messages == {}
    ensures name == old(name)
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
  //ghost var ContentSet: multiset<Message>
  
  // abstract function returning all system mailboxes in one set
  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent, spam} }

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox
  var spam: Mailbox
  var spamFilter: set<Address>
  var userAddresses: set<Address>

  // userboxList implements userBoxes 
  var userboxList: List<Mailbox>

  /*ghost function Contents(): multiset<Message>
    reads this, inbox, drafts, spam, sent, trash, userBoxes
  {
    multiset(inbox.messages) + multiset(drafts.messages) + multiset(spam.messages) + multiset(sent.messages) + multiset(trash.messages) + ContentsAux(userBoxes)
  }

  ghost function ContentsAux(currBoxes: set<Mailbox>): multiset<Message>
  reads currBoxes
  {
    if currBoxes == {} then
      multiset{}
    else
      var mb :| mb in currBoxes;
      multiset(mb.messages) + ContentsAux(currBoxes - {mb})
  }*/

  // Class invariant
  ghost predicate isValid()
  reads this, inbox, spam, sent, drafts, trash, inbox.messages, sent.messages, drafts.messages
  {
    // replace each `true` by your formulation of the invariants 
    // described below
    //----------------------------------------------------------
    // Abstract state invariants
    //----------------------------------------------------------
    // 1. all system mailboxes (inbox, ..., sent) are distinct
    && |systemBoxes()| == 5

    // 2. none of the system mailboxes are in the set
    //    of user-defined mailboxes
    && systemBoxes() * userBoxes == {}
    && (forall m :: m in inbox.messages ==> m.sender !in spamFilter)
    && (forall m :: m in sent.messages ==> m.sender !in spamFilter)
    && (forall m :: m in drafts.messages ==> m.sender !in spamFilter)
    && userAddresses * spamFilter == {}

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
  ensures fresh(spam) && spam.name == "Spam" && spam.messages == {}         // Ensures sent has just been created with no messages and named "Sent"
  ensures userBoxes == {}
  ensures spamFilter == {}
  ensures userAddresses == {}

  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    spam := new Mailbox("Spam");
    spamFilter := {};
    userAddresses := {};
    userboxList := Nil;

    userBoxes := {};
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
  modifies this

  requires isValid()
  requires mb in userBoxes // Ensures that we will only try to delete a mailbox that actually exists in userBoxes

  ensures userBoxes == old(userBoxes) - {mb}
  ensures systemBoxes() == old(systemBoxes())
  ensures spamFilter == old(spamFilter)
  ensures isValid()
  {
    userBoxes := userBoxes - {mb};

    userboxList := remove(userboxList, mb);
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
  modifies this

  requires isValid()
  requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n       // there is no mailbox in userBoxes called n

  ensures exists mb: Mailbox :: fresh(mb) &&                            // mb has just been created
                                mb.name == n &&                         // mb is called n
                                userBoxes == old(userBoxes) + {mb} &&   // the only new mailbox in userBoxes is mb
                                mb.messages == {}                       // mb has no messages in it
  ensures systemBoxes() == old(systemBoxes())
  ensures spamFilter == old(spamFilter)
  ensures isValid()
  {
    var mb := new Mailbox(n);
    userBoxes := userBoxes + {mb};

    userboxList := Cons(mb, userboxList);
  }


  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address) returns (m: Message)
  modifies this, drafts

  requires isValid()
  requires s !in spamFilter

  //ensures exists m: Message :: fresh(m) &&                                        // m has just been created
  //                             drafts.messages == old(drafts.messages) + {m} &&   // the only message added to drafts was m
  //                             m.sender == s                                      // s is the sender of m
  ensures fresh(m)
  ensures drafts.messages == old(drafts.messages) + {m}
  ensures spamFilter == old(spamFilter)
  ensures isValid()
  {
    m := new Message(s);
    drafts.add(m);
  }


  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
  modifies mb1, mb2
  requires isValid()
  requires m in mb1.messages
  requires m !in mb2.messages
  requires mb1 != mb2
  requires (m.sender in spamFilter ==> mb2 in {trash, spam})

  ensures mb1.messages == old(mb1.messages) - {m}  // m is removed from mb1
  ensures mb2.messages == old(mb2.messages) + {m}  // m is added to mb2
  ensures mb1.name == old(mb1.name)                // name of mb1 remains the same
  ensures mb2.name == old(mb2.name)                // name of mb2 remains the same
  ensures spamFilter == old(spamFilter)
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
  requires m in mb.messages
  requires m !in trash.messages
  requires mb != trash
  requires mb != spam // MIGHT CHANGE

  ensures mb.messages == old(mb.messages) - {m}        // m is removed from mb
  ensures trash.messages == old(trash.messages) + {m}  // m is added to trash
  ensures mb.name == old(mb.name)                      // name of mb remains the same
  ensures trash.name == old(trash.name)                // name of trash remains the same
  ensures spamFilter == old(spamFilter)
  ensures isValid()
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
  modifies drafts, sent
  requires isValid()
  requires m in drafts.messages
  requires m !in sent.messages
  requires |m.recipients| > 0
  requires m.sender in userAddresses
  requires drafts != sent

  ensures drafts.messages == old(drafts.messages) - {m}  // m is removed from drafts
  ensures sent.messages == old(sent.messages) + {m}      // m is added to sent
  ensures drafts.name == old(drafts.name)                // name of drafts remains the same
  ensures sent.name == old(sent.name)                    // name of sent remains the same
  ensures spamFilter == old(spamFilter)
  ensures isValid()

  {
    moveMessage(m, drafts, sent);
  }

  method getMessage(m: Message)
  modifies inbox
  requires isValid()
  requires m !in inbox.messages
  requires exists i :: 0 <= i < |m.recipients| && m.recipients[i] in userAddresses
  requires m.sender !in spamFilter
  
  ensures inbox.messages == old(inbox.messages) + {m}
  ensures spamFilter == old(spamFilter)
  ensures isValid()
  {
    inbox.messages := inbox.messages + {m};
  }

  // Empties the trash mailbox
  method emptyTrash ()
  modifies trash
  requires isValid()
  requires trash.messages != {} // Ensures that we are not emptying an empty trash
  ensures trash.messages == {}
  ensures trash.name == old(trash.name)
  ensures spamFilter == old(spamFilter)
  ensures isValid()
  {
    trash.empty();
  }

  method filterMailbox(mb: Mailbox) returns (filtered: Mailbox)
  modifies spam
  //requires isValid()

  ensures filtered.messages == (set m | m in mb.messages && m.sender !in spamFilter :: m)
  ensures fresh(filtered)
  //ensures isValid()
  {
    filtered := new Mailbox(mb.name);
    var oldMessages := mb.messages;

    while oldMessages != {}
      decreases oldMessages
      invariant oldMessages <= mb.messages
      invariant oldMessages * filtered.messages == {}
      invariant filtered.messages == (set m | m in mb.messages - oldMessages && m.sender !in spamFilter :: m)
    {
      var message :| message in oldMessages;
      if (message.sender !in spamFilter) {
        filtered.add(message);
      }
      else if (message !in spam.messages) {
        spam.add(message);
      }
      oldMessages := oldMessages - {message};
    }
  }

  method addToSpam(a: Address)
  modifies this, inbox, spam
  requires isValid()
  requires a !in spamFilter
  requires a !in userAddresses

  ensures spamFilter == old(spamFilter) + {a}
  ensures isValid()
  {
    spamFilter := spamFilter + {a};
    inbox := filterMailbox(inbox);
    sent := filterMailbox(sent);
    drafts := filterMailbox(trash);
  }

  method removeFromFilter(a: Address)
  modifies this
  requires isValid()
  requires a in spamFilter
  ensures spamFilter == old(spamFilter) - {a}
  ensures isValid()
  {
    spamFilter := spamFilter - {a};
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
  var m := ma.newMessage(s);        
  assert exists nw: Message :: ma.drafts.messages == {nw} == {m};
}

