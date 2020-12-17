--define time as POSIX or date, time, hours etc.? Ok, I've chosen the "yyyy-mm-dd hh:mm" way.
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
    Location: one Location,
    opensAt: some RelativeTime,
    closesAt: some RelativeTime,
    twentyfour: one Bool
}{
    twentyfour=False implies (#opensAt>0 && #closesAt>0 && #opensAt=#closesAt)
    twentyfour=True implies (#opensAt=0 && #closesAt=0)
}

abstract sig Person {
    name: seq Char,
    surname: seq Char,
    fc: seq Char,
    customerId: seq Char,
    tickets: set Ticket,
    reservations: set BookingReservation
}{
    #name>2
    #surname>2
    //#fc>=11
    //#customerId=12
}

one sig Now{
    now: one Time
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
    time: one Time,
    at: one Store,
    durationMinutes: one Int,
    id: seq Char
}{
    durationMinutes>0
}

sig Ticket{
    owner: one Person,
    parentQueue: Queue, --identifies parent Queue
    id: seq Char,
    prestoCode: seq Char,
    entranceTime: one Time,
    valid: Bool
}{
    #this.@id>0
}

sig Queue{
    members: seq Ticket,
    store: one Store, -- each queue refers to a specific store, 1 store <--> 1 queue
    id: seq Char --each queue has an ID
}{
    #members>0
    #this.@id>0 -- TODO
}

one sig Queues{
    queuesList: set Queue
}

one sig CustomerDB{
    customers: set Customer
}

one sig StaffDB{
    staffMembers: set StaffMember
}

one sig Bookings{
    bookingsList: set BookingReservation
}

one sig StoresDB{
    storesList: set Store
}

--facts----------------------------------------
fact fiscalCodeIsUnique{
    all disj pers,pers1 : Person | pers.fc != pers1.fc
}

fact noReservationInPast{
    all reservation : BookingReservation | aTimeBeforeB[Now.now, reservation.time]
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
    all t: Ticket | some q: Queue | q=t.parentQueue
}
fact twoWayCorrespondanceTicketQueueID{
    all t: Ticket | all q: Queue | t.parentQueue=q iff t in q.members.elems
}

fact twoWayCorrespondanceTicketOwner{
    all t:Ticket, p:Person | (t.owner=p implies t in p.tickets) && (t in p.tickets implies t.owner=p)
}

fact eachOpeningDayHasAlsoClosing{
    all s:Store| all o:RelativeTime | o in s.opensAt implies 
    (one c:RelativeTime | c.validDay=o.validDay && c in s.closesAt)
}

fact closingTimeAfterOpening{
    all s:Store | s.twentyfour=False implies (all o,c: RelativeTime| 
    (o in s.opensAt && c in s.closesAt && o.validDay=c.validDay) implies aRelativeTimeBeforeB[o, c])
}

--functions------------------------------------
fun retrieveTicketsStore[t:Ticket]: one Store {
    t.parentQueue.store
}

--predicates ----------------------------------
pred isCustomer[p:Person]{
    p in CustomerDB.customers
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
    some r: BookingReservation | r in Bookings.bookingsList && r.applicant=p
}

pred hasTicket[p: Person]{
    some q: Queue | some t: Ticket | t.owner=p && t in q.members.elems
}

pred hasTicketForThisStore[p: Person, s: Store]{
    some t: Ticket | t in p.tickets && retrieveTicketsStore[t]=s
}

pred allowUserIn[p:Person, thisStore: Store]{
    some t: Ticket| hasTicketForThisStore[p, thisStore] && t.valid=True
}

//adding a reservation
pred book[b, b': Bookings, a: Person, t:Time, store: Store, duration: Int]{
    b'.bookingsList.applicant = b.bookingsList.applicant +a
    b'.bookingsList.time= b.bookingsList.time + t
    b'.bookingsList.at= b.bookingsList.at + store
    b'.bookingsList.durationMinutes= b.bookingsList.durationMinutes + duration
}

pred getQuickTicket[q, q': Queues, a: Person, t:Time, s: Store]{
    q'.queuesList.members.elems.owner = q.queuesList.members.elems.owner + a
    q'.queuesList.members.elems.entranceTime= q.queuesList.members.elems.entranceTime+t
    q'.queuesList.store= q.queuesList.store + s
    (all ticket: Ticket | (ticket.owner=a&&ticket.entranceTime=t)implies ticket.valid=True)//new tickets are valid

}

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
    all p: Person, s: Store | !hasTicketForThisStore[p,s] implies !allowUserIn[p, s]
}

assert getQuickTicketGrantsEnter{
    all disj p: Person, disj t:Time, disj s:Store, disj q,q': Queues | getQuickTicket[q, q',p, t, s] implies allowUserIn[p,s]
}

--checks---------------------------------------
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
run {some s: Store | s.twentyfour=False} for 7 Int

