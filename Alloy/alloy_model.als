--define time as POSIX or date, time, hours etc.? Ok, I've chosen the "yyyy-mm-dd hh:mm" way.

enum Day{Monday, Tuesday, Wednesday, Thrusday, Friday, Saturday, Sunday}

sig Date{
    year: Int,
    month: Int,
    day: Int,
}{
    year>0 && year<=3000,
    month>0 && month<13,
    day>0 && day<32
}

sig Time{
    date: Date
    hour: Int, 
    minutes: Int
    seconds: Int
}{
    hour<25 && hour >=0,
    minutes<60 && minutes>=0,
    seconds<60 && seconds>=0
}

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

abstract sig Person {
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

one sig Now{
    now: one Time
}

sig Customer extends Person{}

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
    all reservation : BookingReservation | aTimeBeforeB(Now.now, reservation.time)
}

fact noDuplicatedCustomers{
    all disj cust,cust1: Person | cust,cust1 in Queues.queuesList.members | cust!=cust1
}

fact dayConsistency{ --we should also handle leap years...
    all date : Date | (date.month=11 ||date.month=4 || date.month=6 || date.month=9) implies date.day<31 && 
    (date.month=2) implies date.day<30   
}

fact noDBMismatch{-- fact that a person must either be Customer or Staff should be guaranteed by abstract Person (omitting: &&(isCustomer(p)||isStaff(p)) )
    all p : Person | (isCustomer(p) implies !isStaff(p)) && (isStaff(p) implies !isCustomer(p))
}


--predicates ----------------------------------
pred isCustomer[p:Person]{
    p in CustomerDB.customers 
}

pred isStaff[p:Person]{
    p in StaffDB.staffMembers
}

pred aDateBeforeB[a, b: Date]{
    a.year<b.year||(a.year=b.year && a.month< b.month)||(a.year=b.year && a.month= b.month&&a.day<b.day)
}


pred aTimeBeforeB[a, b : Time]{
    aDateBeforeB(a.date, b.date)|| (a.dateb=b.date && a.hour<b.hour) || (a.date=b.date && a.hour=b.hour && a.minutes<b.minutes) || 
    (a.date=b.date && a.hour=b.hour && a.minutes=b.minutes&&a.seconds<b.seconds)

}

pred userHasBooked[p: Person]{
    some r: BookingReservation in bookings | r.applicant=p
}

--assertions-----------------------------------
assert customersInCustomersDB(c:Customer){
    isCustomer(c) 
}

assert StaffMembersInStaffDB(s:StaffMember){
    isStaff(s)
}


--checks---------------------------------------
check 