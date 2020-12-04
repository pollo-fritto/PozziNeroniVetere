--define time as POSIX or date, time, hours etc.?
sig Time{}

sig RelativeTime{
    validDays: set Day,
    hour: one Int
    minutes: one Int
    seconds: one Int
}{
    hour<25 && hour >=0,
    minutes<60 && minutes>=0,
    seconds<60 && seconds>=0
}

sig Location{
    latitude: one Int
    longitude: one Int
}

sig Store{
    commercialName: one String,
    longName: lone String,
    Location: Location,
    opensAt: lone RelativeTime,
    closesAt: lone RelativeTime,
    twentyfour: one Bool,

}

sig Person {
    name: one String,
    surname: one String,
    fc: lone String,
    customerId: one String
}
{
    name.length>2,
    surname.length>2,
    fc.length=11
}

sig Now{
    now: one Time
}

sig StaffMember extends Person{
    cardID: one String,
    nowWorkingAt: one Store,
    active: one Bool,
    level: one Int

}

sig BookingReservation {
    applicant: one Person,
    time: one Time,
    at: one Store,
    duration: one Int,
    id: one String,
}

sig Ticket{

}

sig Queue{
    members: set Person,
    store: one Store,
    id: one String
}

sig Queues{
    queuesList: set Queue
}

one sig CustomerDB{
    customers: set Person
}

one sig StaffDB{
    staffMembers: set StaffMember
}

one sig Bookings{
    bookings: set BookingReservation
}

one sig StoresDB{
    storesList: set Store
}
--facts----------------------------------------
fact fiscalCodeIsUnique{
    all disj pers,pers1 : Person | pers.fc != pers1.fc
}

fact noReservationInPast{
    all reservation : BookingReservation | reservation.time>Now.now -- how do we define time> time? TODO
}

fact noDuplicatedCustomers{
    all disj cust,cust1: Person | cust,cust1 in Queues.queuesList.members | cust!=cust1
}
--predicates ----------------------------------
pred isCustomer(p:Person){
    p in CustomerDB.customers
}

pred isStaff(p:Person){
    p in StaffDB.staffMembers
}

--assertions-----------------------------------
assert delUndoAdd {
  all b,b',b'': Book, n: Name , a:Addr | add[b,b',n,a] and del[b',b'',n] implies b.addr = b''.addr
}



check delUndoAdd for 3
