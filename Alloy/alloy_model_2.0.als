
enum Day{Monday, Tuesday, Wednesday, Thrusday, Friday, Saturday, Sunday}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
sig Char{} -- using this to be able to write constraints on strings length
sig Float{
    integer: Int,
    decimal: Int
}{
    decimal>0
}

sig Date{
    year: Int,
    month: Int,
    day: Int,
}{
    year>0 
    --year<=3000 //we can't say this with <=10 bits for Int
    month>0 
    month<13
    day>0 
    day<32
}

sig Time{
    date: Date,
    hour: Int, 
    minutes: Int,
    seconds: Int,
}{
    hour<24 
    hour>=0
    minutes<60 
    minutes>=0
    seconds<60 
    seconds>=0
}

sig RelativeTime{
    validDay: one Day,
    hour: one Int,
    minutes: one Int,
    seconds: one Int,
}{
    hour<24 
    hour>=0
    minutes<60 
    minutes>=0
    seconds<60 
    seconds>=0
}

sig Location{
    latitude: one Float,
    longitude: one Float
}/*{ --it'd be nice, but solver doesn't let us
    latitude.integer<85
    latitude.integer>-85
    longitude.integer<180
    longitude.integer>-180
}*/

sig Store{
    commercialName: seq Char,
    longName: seq Char,
    location: one Location,
    opensAt: set RelativeTime,
    closesAt: set RelativeTime,
    twentyfourSeven: one Bool, 
    occupantsMax: one Int
}{
    twentyfourSeven=False implies (#opensAt>0 && #closesAt>0 && #opensAt=#closesAt)
    twentyfourSeven=True implies (#opensAt=0 && #closesAt=0)
    occupantsMax>0
}

abstract sig Person {
    name: seq Char,
    surname: seq Char,
    fc: seq Char,
    customerId: seq Char,
    tickets: set Ticket,
    reservations: set BookingReservation,
    currentLocation: lone Location //used for timed notifications
}{
    #name>2
    #surname>2
    //#fc>=11
    //#customerId=12
}

one sig Now{
    time: one Time
}

sig Customer extends Person{}

sig StaffMember extends Person{
    cardID: seq Char,
    nowWorkingAt: one Store,
    active: one Bool,
    level: one Int
}{
    #cardID>3
    level>0
}

sig BookingReservation {
    applicant: one Person,
    startTime: one Time,
    where: one Store,
    endTime: one Time,
    id: seq Char
}{
    //aTimeBeforeB[startTime, endTime]
}

sig Ticket{
    owner: one Person,
    parentQueue: Queue, --identifies parent Queue
    id: seq Char,
    prestoCode: seq Char,
    entranceTime: one Time,
    valid: one Bool, 
    active: one Bool,
    scannedIn: lone Time,
    scannedOut: lone Time
}{
    #this.@id>0
}

sig Notification{
    recipient : one Person,
    message: seq Char,
    disposal : one Time //when are we sending this notification
}

sig Queue{
    members: seq Ticket,
    store: one Store, -- each queue refers to a specific store, 1 store <--> 1 queue
    id: seq Char, --each queue has an ID
    estimatedNextEntrance: lone Time
}{
    #members>0
    #this.@id>0 -- TODO
}

one sig NotificationsDB{
    notifications: set Notification
}

one sig Queues{
    queuesList: set Queue
}

one sig CustomersDB{
    customers: set Customer
}

one sig StaffDB{
    staffMembers: set StaffMember
}

one sig BookingsDB{
    bookingsList: set BookingReservation
}

one sig StoresDB{
    storesList: set Store
}

--facts----------------------------------------
fact userAndFiscalCodesUnique{
    all disj pers,pers1 : Person | pers.fc != pers1.fc && pers.customerId!=pers1.customerId
}

fact reservationConsistency{
    all r: BookingReservation | r.startTime.date=r.endTime.date && aTimeBeforeB[r.startTime, r.endTime]
}

fact noDuplicatedCustomers{
    all disj cust,cust1: Person | cust.customerId !=cust1.customerId
}

fact dayConsistency{ --we should also handle leap years...
    all date : Date | (date.month=11 ||date.month=4 || date.month=6 || date.month=9) implies date.day<31 && 
    (date.month=2) implies date.day<30   
}

fact noDBMismatch{
    all p : Person | (isCustomer[p] implies !isStaff[p]) && (isStaff[p] implies !isCustomer[p])
}

fact allPeoplesBelongToDB{
    all p: Person | isCustomer[p] || isStaff[p]
}

fact allStoresBelongToDB{
    all s: Store | s in StoresDB.storesList
}

fact allNotificationsBelongToDB{
    all n: Notification| n in NotificationsDB.notifications
}

/*fact allQueuesBelongToDB{
    all q: Queue | q in Queues.queuesList
}*/

fact eachStoreOneQueueMax{
    all disj q, q1 : Queue | q.store!=q1.store
}

fact noDuplicatedTickets{
    all q: Queue | !q.members.hasDups
}

fact userHasNoMultipleTicketsSameDay{
    all disj t,t1: Ticket| (t.owner=t1.owner && t.valid=True && t1.valid=True) implies 
    (aDateBeforeB[t.entranceTime.date, t1.entranceTime.date]||aDateBeforeB[t1.entranceTime.date, t.entranceTime.date])
}

fact eachTicketHasParentQueue{
    all t: Ticket | one q: Queue | q=t.parentQueue
}

fact eachReservationHasApplicant{
    all r: BookingReservation | one p: Person | p=r.applicant
}

fact twoWayCorrespondanceTicketQueue{
    all t: Ticket | all q: Queue | t.parentQueue=q iff t in q.members.elems
}

fact twoWayCorrespondanceReservationOwner{
    all r:BookingReservation | all p: Person | r.applicant=p iff r in p.reservations
}

fact twoWayCorrespondanceTicketOwner{
    all t:Ticket, p:Person | (t.owner=p implies t in p.tickets) && (t in p.tickets implies t.owner=p)
}

fact onlyOneBookingPerDayPerUser{
    all disj b, b1: BookingReservation | !(b.startTime.date=b1.startTime.date && b.applicant=b1.applicant)
}

fact eachOpeningDayHasAlsoClosing{
    all s:Store| all o:RelativeTime | o in s.opensAt implies 
    (one c:RelativeTime | c.validDay=o.validDay && c in s.closesAt)
}

fact closingTimeAfterOpening{
    all s:Store | s.twentyfourSeven=False implies (all o,c: RelativeTime| 
    (o in s.opensAt && c in s.closesAt && o.validDay=c.validDay) implies aRelativeTimeBeforeB[o, c])
}

--functions------------------------------------
fun retrieveTicketsStore[t:Ticket]: one Store {
    t.parentQueue.store
}

fun getCurrOccupants[q: Queue]: one Int {
    #{t: Ticket | t.active=True && t in q.members.elems}
}

fun getBookedOccupants[s: Store, start:Time, end:Time] : one Int{
    #{x: BookingReservation | x.where = s && (sameTime[start, x.startTime]|| aTimeBeforeB[start, x.startTime]) 
    && (sameTime[x.startTime, end] || aTimeBeforeB[x.endTime, end])}
    //number of reservations whose start time >= start and end time <= end
}

fun computeDisposalTime[ticketTime: Time, userLocation: Location]: one Time{
    {x: Time}
}

--predicates ----------------------------------
pred isCustomer[p:Person]{
    p in CustomersDB.customers
}

pred isStaff[p:Person]{
    p in StaffDB.staffMembers
}

pred aDateBeforeB[a:Date , b: Date]{
    a.year<b.year||(a.year=b.year && a.month< b.month)||(a.year=b.year && a.month= b.month&&a.day<b.day)
}

pred aRelativeTimeBeforeB[a,b:RelativeTime]{
    a.validDay=b.validDay && ((a.hour<b.hour) || (a.validDay=b.validDay && a.hour=b.hour && a.minutes<b.minutes) || 
    (a.validDay=b.validDay && a.hour=b.hour && a.minutes=b.minutes&&a.seconds<b.seconds))
}

pred aTimeBeforeB[a: Time, b: Time]{
    aDateBeforeB[a.date, b.date]|| (a.date=b.date && a.hour<b.hour) || (a.date=b.date && a.hour=b.hour && a.minutes<b.minutes) || 
    (a.date=b.date && a.hour=b.hour && a.minutes=b.minutes&&a.seconds<b.seconds)

}

pred sameTime[a, b : Time]{
    !(aTimeBeforeB[a,b]||aTimeBeforeB[b, a])
}

pred userHasBooked[p: Person]{
    some r: BookingReservation | r in BookingsDB.bookingsList && r.applicant=p
}

pred hasTicket[p: Person]{
    some q: Queue | some t: Ticket | t.owner=p && t in q.members.elems
}

pred maxOccupantsNotExceeded[s: Store]{
    all q: Queue| q.store = s implies plus[getCurrOccupants[q], 1]<s.occupantsMax
}

pred bookingsNotExceedingMaxOccupants[s: Store, start: Time, end: Time]{
    getBookedOccupants[s, start, end]+1<=s.occupantsMax
}

pred hasTicketForThisStore[p: Person, s: Store]{
    some t: Ticket | t in p.tickets && retrieveTicketsStore[t]=s
}

pred activateTicket[t : Ticket]{
    t.active=True && t.scannedIn=Now.time
}

pred expireTicket[t: Ticket]{
    t.active=False && t.scannedOut=Now.time && t.valid=False
}

pred allowUserIn[p:Person, thisStore: Store]{
     //ensures we're not going to exceed store's capacity with a new ticket
    maxOccupantsNotExceeded[thisStore] && (some t: Ticket| hasTicketForThisStore[p, thisStore] && t.valid=True 
    && activateTicket[t]) //activates ticket to track user's entrance/exit
}

//adding a reservation
pred book[b, b': BookingsDB, a: Person, start:Time, store: Store, end: Time]{
    bookingsNotExceedingMaxOccupants[store, start, end]//ensures we're not going to exceed store's capacity with new bookings
    aTimeBeforeB[Now.time, start] //we don't want reservations in the past
    b'.bookingsList.applicant = b.bookingsList.applicant +a
    b'.bookingsList.startTime= b.bookingsList.startTime + start
    b'.bookingsList.where= b.bookingsList.where + store
    b'.bookingsList.endTime= b.bookingsList.endTime + end
}


pred getQuickTicket[q, q': Queues, a: Person, t:Time, s: Store]{
    q'.queuesList.members.elems.owner = q.queuesList.members.elems.owner + a
    q'.queuesList.members.elems.entranceTime= q.queuesList.members.elems.entranceTime+t
    q'.queuesList.store= q.queuesList.store + s
    (all ticket: Ticket | (ticket.owner=a&&ticket.entranceTime=t)implies ticket.valid=True)//new tickets are valid
    (some v1, v2: NotificationsDB | { //generate notifications accordingly
        v2.notifications.recipient=v1.notifications.recipient + a
        v2.notifications.disposal=v1.notifications.disposal + computeDisposalTime[t, a.currentLocation]
    })
}

pred deleteQuickTicket[q, q': Queues, t: Ticket]{
    q'.queuesList.members.elems.owner = q.queuesList.members.elems.owner - t.owner
    q'.queuesList.members.elems.entranceTime= q.queuesList.members.elems.entranceTime - t.entranceTime
    (#q'.queuesList.members.t>=1) || (q'.queuesList.store= q.queuesList.store - retrieveTicketsStore[t])
    (all ticket: Ticket | (ticket.owner=t.owner&&ticket.entranceTime=t.entranceTime)implies ticket.valid=False)//old tickets are invalid
}

pred temporaryStopStore[s: Store]{
    all q: Queue, t : Ticket | (q.store = s && t in q.members.elems) implies t.valid=False
}

pred exitStore[t: Ticket]{
    expireTicket[t] && (some q, q': Queues | deleteQuickTicket[q, q', t])
}


pred notificationDispatch{
    all n: Notification| aTimeBeforeB[n.disposal, Now.time] implies sendNotification[n]
}

pred sendNotification[n: Notification]{}

--assertions-----------------------------------
assert customersInCustomersDB{
    all c: Customer | isCustomer[c]
}

assert staffMembersInStaffDB{
    all s: StaffMember | isStaff[s]
}

assert noOrphanTicket{
    no t: Ticket | some p: Person | t.owner=p && !hasTicket[p]
}

assert noTicketNoEntry{
    no p: Person, s: Store | !hasTicketForThisStore[p,s] && allowUserIn[p, s]
}

assert getQuickTicketGrantsEnter{
    all p: Person, t:Time, s:Store, disj q,q': Queues | getQuickTicket[q, q',p, t, s] implies allowUserIn[p,s]
}

assert generateTicketDoesNotExceedMaxOccupants{
    all p: Person, t:Time, s:Store, disj q,q': Queues | getQuickTicket[q, q',p, t, s] implies maxOccupantsNotExceeded[s]
}

assert bookingDoesNotExceedMaxOccupants{
    all p: Person, s,e :Time, st:Store, disj b,b': BookingsDB | book[b, b', p, s, st, e] implies bookingsNotExceedingMaxOccupants[st, s, e]
}

assert neverAllowInMoreThanMax{
    no p:Person, s:Store | allowUserIn[p, s] && !maxOccupantsNotExceeded[s]
}

assert delUndoesAdd{
    all disj q, q', q'': Queues, p: Person, t: Time, s: Store, ticket: Ticket | 
    (ticket.owner=p && ticket.entranceTime=t && getQuickTicket[q, q', p, t, s] && deleteQuickTicket[q', q'', ticket])
    implies
    (q.queuesList.members = q''.queuesList.members)
}

--commands---------------------------------------
check delUndoesAdd for 7 Int
check neverAllowInMoreThanMax for 7 Int
check bookingDoesNotExceedMaxOccupants for 7 Int
check generateTicketDoesNotExceedMaxOccupants for 7 Int
check getQuickTicketGrantsEnter for 7 but 7 Int
check customersInCustomersDB for 7 Int
check staffMembersInStaffDB for 7 Int
check noOrphanTicket for 7 Int
check noTicketNoEntry for 7 Int
run {some t: Ticket | t.valid=True} for 7 Int
run hasTicket for 7 Int
run hasTicketForThisStore for 7 Int
run {some p:Person | hasTicket[p] && isCustomer[p]} for 7 Int
run {some p:Person | hasTicket[p] && isStaff[p]} for 7 Int
run {some p:Person, s:Store | allowUserIn[p,s] && isStaff[p]} for 7 Int
run {some p:Person, s:Store | allowUserIn[p,s] && isCustomer[p]} for 7 Int
run userHasBooked for 7 Int
run isCustomer for 7 Int
run isStaff for 7 Int
run aDateBeforeB for 7 Int
run book for 7 Int
run getQuickTicket for 7 Int
run {some s, s1: Store | s.twentyfourSeven=True && s1.twentyfourSeven=False} for 7 Int
run aTimeBeforeB for 7 Int
run maxOccupantsNotExceeded for 7 Int
run temporaryStopStore for 7 Int
run notificationDispatch for 7 Int
run exitStore for 7 Int
run deleteQuickTicket for 7 Int 

/* v2.0 Useful additions:
- bookings constraints and 2-way correspondances with applicant [DONE]
- no overcrowding: [DONE]
    - store capacity [DONE]
    - check when creating new ticket [DONE]
    - check when booking [DONE]
- exit from store deactivates ticket [DONE]
- delete ticket when deactivated [DONE]
- staff:
    - temporary deactivate store [DONE]
- notifications:
    - add location to the customer [DONE]
    - add queue estimated next entrance [DONE]
- goal-related assertions (no overcrowding, no multiple tickets etc) [DONE]
*/
