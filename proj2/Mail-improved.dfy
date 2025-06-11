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
    requires m !in messages                     // Ensures that we will not add a repeated message to the same mailbox
    ensures messages == old(messages) + {m}     // The only change to messages is the addition of m
    ensures name == old(name)                   // Mailbox's name remains the same
  {    
    messages := messages + { m };
  }

  // Removes message m from mailbox
  // m need not be in the mailbox 
  method remove(m: Message)
    modifies this
    ensures messages == old(messages) - {m}     // The only change to messages is the removal of m
    ensures name == old(name)                   // Mailbox's name remains the same
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
  // abstract fields
  ghost var userBoxes: set<Mailbox>
  ghost var spamFilter: set<Address>
  ghost var userAddresses: set<Address>
  
  // abstract function returning all system mailboxes in one set
  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent, spam} }

  ghost function allMessages(): set<Message>
    reads this, inbox, drafts, trash, sent, spam, userBoxes
  { inbox.messages + drafts.messages + trash.messages + sent.messages + spam.messages + messages(userBoxes)}

  ghost function messages(currBoxes: set<Mailbox>): set<Message>
    reads currBoxes
  {
    if currBoxes == {} then {}
    else
      var mb :| mb in currBoxes;
      mb.messages + messages(currBoxes - {mb})
  }

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox
  var spam: Mailbox

  // userboxList implements userBoxes 
  var userboxList: List<Mailbox>

  // spamList implements spamFilter 
  var spamList: List<Address>

  // addressesList implements userAddresses 
  var addressesList: List<Address>

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
    && |systemBoxes()| == 5

    // 2. none of the system mailboxes are in the set
    //    of user-defined mailboxes
    && systemBoxes() * userBoxes == {}

    // 3. none of the user addresses are in the set
    //    of spam addresses
    && spamFilter * userAddresses == {}
      
    //----------------------------------------------------------
    // Abstract-to-concrete state invariants
    //----------------------------------------------------------
    // userBoxes is the set of mailboxes in userboxList
    && userBoxes == elements(userboxList)
    // spamSet is the set of addresses in spamList
    && spamFilter == elements(spamList)
    // userAddresses is the set of addresses in addressesList
    && userAddresses == elements(addressesList)
  }

  constructor (addr : List<Address>)
  requires addr != Nil                                                      // A MailApp with no address cannot be created

  ensures isValid()
  ensures fresh(inbox) && inbox.name == "Inbox" && inbox.messages == {}     // Ensures inbox has just been created with no messages and named "Inbox"
  ensures fresh(drafts) && drafts.name == "Drafts" && drafts.messages == {} // Ensures drafts has just been created with no messages and named "Drafts"
  ensures fresh(trash) && trash.name == "Trash" && trash.messages == {}     // Ensures trash has just been created with no messages and named "Trash"
  ensures fresh(sent) && sent.name == "Sent" && sent.messages == {}         // Ensures sent has just been created with no messages and named "Sent"
  ensures fresh(spam) && spam.name == "Spam" && spam.messages == {}         // Ensures spam has just been created with no messages and named "Spam"
  ensures userBoxes == {}                                                   // Ensures there are no user boxes
  ensures spamFilter == {}                                                  // Ensures there are no addresses in the spamFilter
  ensures userAddresses == elements(addr)                                   // The user addresses are the ones received as input
  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    spam := new Mailbox("Spam");
    userboxList := Nil;
    spamList := Nil;
    addressesList := addr;

    userBoxes := {};
    spamFilter := {};
    userAddresses := elements(addr);
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
  modifies this

  requires isValid()
  requires mb in userBoxes                        // Ensures that we will only try to delete a mailbox that actually exists in userBoxes

  ensures userBoxes == old(userBoxes) - {mb}      // The only change to userBoxes is the removal of mb
  ensures inbox == old(inbox)                     // inbox remains the same
  ensures drafts == old(drafts)                   // drafts remains the same
  ensures sent == old(sent)                       // sent remains the same
  ensures trash == old(trash)                     // trash remains the same
  ensures spam == old(spam)                       // spam remains the same
  ensures userAddresses == old(userAddresses)     // userAddresses remains the same
  ensures spamFilter == old(spamFilter)           // spamFilter remains the same
  ensures isValid()
  {
    userboxList := remove(userboxList, mb);

    userBoxes := userBoxes - {mb};
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string) returns (mb: Mailbox)
  modifies this

  requires isValid()
  requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n       // There is no mailbox in userBoxes called n

  ensures fresh(mb) &&                                                  // mb has just been created
          mb.name == n &&                                               // mb is called n
          userBoxes == old(userBoxes) + {mb} &&                         // The only new mailbox in userBoxes is mb
          mb.messages == {}                                             // mb has no messages in it
  ensures inbox == old(inbox)                                           // inbox remains the same
  ensures drafts == old(drafts)                                         // drafts remains the same
  ensures sent == old(sent)                                             // sent remains the same
  ensures trash == old(trash)                                           // trash remains the same
  ensures spam == old(spam)                                             // spam remains the same
  ensures userAddresses == old(userAddresses)                           // userAddresses remains the same
  ensures spamFilter == old(spamFilter)                                 // spamFilter remains the same
  ensures isValid()
  {
    mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);

    userBoxes := userBoxes + {mb};
  }


  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address) returns (m: Message)
  modifies drafts
  requires isValid()

  ensures fresh(m)                                        // m has just been created
  ensures drafts.messages == old(drafts.messages) + {m}   // the only message added to drafts was m
  ensures m.sender == s                                   // s is the sender of m
  ensures drafts.name == old(drafts.name)                 // drafts name remains the same
  ensures isValid()
  {
    m := new Message(s);
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
  requires m.sender in userAddresses                     // Only the owner of the MailApp can send emails

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

  // Receives a message from the exterior
  method getMessage(m: Message)
  modifies inbox, spam
  requires isValid()
  requires m !in allMessages()
  requires exists i :: 0 <= i < |m.recipients| && m.recipients[i] in userAddresses
  
  ensures if (m.sender in spamFilter) then
            (spam.messages == old(spam.messages) + {m} &&
             inbox.messages == old(inbox.messages))
          else
            (inbox.messages == old(inbox.messages) + {m} &&
             spam.messages == old(spam.messages))
  ensures inbox.name == old(inbox.name)
  ensures spam.name == old(spam.name)
  ensures isValid()
  {
    
    if (contains(spamList, m.sender)) {
      spam.messages := spam.messages + {m};
    }
    else {
      inbox.messages := inbox.messages + {m};
    }
  }

  method addToSpam(a: Address)
  modifies this
  requires isValid()
  requires a !in userAddresses
  requires a !in spamFilter
  ensures spamFilter == old(spamFilter) + {a}
  ensures inbox == old(inbox)
  ensures drafts == old(drafts)
  ensures sent == old(sent)
  ensures trash == old(trash)
  ensures spam == old(spam)
  ensures userAddresses == old(userAddresses)
  ensures userBoxes == old(userBoxes)
  ensures isValid()
  {
    spamList := Cons(a, spamList);

    spamFilter := spamFilter + {a};
  }

  method filterMailbox(mb: Mailbox)
  modifies spam, mb
  requires isValid()
  requires mb != spam
  requires mb in systemBoxes() + userBoxes

  ensures forall m :: m in old(mb.messages) && m.sender !in spamFilter ==> m in mb.messages
  ensures forall m :: m in old(mb.messages) && m.sender in spamFilter ==> (m !in mb.messages && m in spam.messages)
  ensures spam.name == old(spam.name)
  ensures mb.name == old(mb.name)
  ensures isValid()
  {
    var oldMessages := mb.messages;

    while oldMessages != {}
      decreases oldMessages
      invariant oldMessages <= mb.messages
      invariant spam.name == old(spam.name)
      invariant mb.name == old(mb.name)
      invariant (forall m :: m in old(mb.messages) - oldMessages && m.sender !in spamFilter ==> m in mb.messages)
      invariant (forall m :: m in old(mb.messages) - oldMessages && m.sender in spamFilter ==> m !in mb.messages && m in spam.messages)
    {
      var message :| message in oldMessages;
      if (contains(spamList, message.sender)) {
        if (message !in spam.messages) {
          moveMessage(message, mb, spam);
        }
        else {
          mb.remove(message);
        }
      }

      oldMessages := oldMessages - {message};
    }
  }

  method removeFromSpam(a: Address)
  modifies this
  requires isValid()
  requires a in spamFilter
  ensures spamFilter == old(spamFilter) - {a}
  ensures inbox == old(inbox)
  ensures drafts == old(drafts)
  ensures sent == old(sent)
  ensures trash == old(trash)
  ensures spam == old(spam)
  ensures userAddresses == old(userAddresses)
  ensures userBoxes == old(userBoxes)
  ensures isValid()
  {
    spamList := remove(spamList, a);

    spamFilter := spamFilter - {a};
  }
}

// Test
/* Can be used to test your code. */

method test() {

  var a := new Address();
  var ma := new MailApp(Cons(a, Nil)); 
  assert ma.inbox.name == "Inbox";
  assert ma.drafts.name == "Drafts";
  assert ma.trash.name == "Trash";
  assert ma.sent.name == "Sent";
  assert ma.inbox.messages == ma.drafts.messages ==
                              ma.trash.messages ==
                              ma.sent.messages == {};

  var umb := ma.newMailbox("students"); 
  assert exists mb: Mailbox :: mb in ma.userBoxes &&
                               mb.name == "students" &&
                               mb.messages == {};

  var s := new Address();
  var m := ma.newMessage(s);        
  assert ma.drafts.messages == {m};

  var spammer := new Address();
  var get := new Message(spammer);
  get.addRecipient(0, a);

  ma.getMessage(get);

  assert get in ma.inbox.messages;

  ma.moveMessage(get, ma.inbox, umb);

  assert get in umb.messages;

  ma.addToSpam(spammer);

  assert get in umb.messages;
  assert get.sender in ma.spamFilter;

  ma.filterMailbox(umb);

  assert get in ma.spam.messages;
  assert get !in umb.messages;

  var initialFilter := new Message(spammer);
  initialFilter.addRecipient(0, a);
  ma.getMessage(initialFilter);
  ma.deleteMailbox(umb);

  assert initialFilter in ma.spam.messages;

  ma.deleteMessage(initialFilter, ma.spam);

  assert initialFilter in ma.trash.messages;
  assert initialFilter !in ma.spam.messages;

  var noLongerFiltered := new Message(spammer);
  noLongerFiltered.addRecipient(0, a);
  ma.removeFromSpam(spammer);

  ma.getMessage(noLongerFiltered);

  assert noLongerFiltered in ma.inbox.messages;

  ma.emptyTrash();

  ma.getMessage(initialFilter);
}

