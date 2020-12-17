/*fun facts about alloy
- run predicates for Int 10 works, because "the default bit width used is 4 so only range -8/7 is generated..." So, solution is to run for >7 Int
- strings don't work either (no instance found)
- constraints on more than 2/3 chars per field lead to problems
*/



--define time as POSIX or date, time, hours etc.? Ok, I've chosen the "yyyy-mm-dd hh:mm" way.
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
sig Float{
    integer: Int,
    decimal: Int
}{
    decimal>0
}
sig Char{} -- using this to be able to write constraints on strings length
enum Day{Monday, Tuesday, Wednesday, Thrusday, Friday, Saturday, Sunday}


sig Date{
    year: Int,
    month: Int,
    day: Int
}{
    year>0
    --year>2020
    --year<=3000
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
    hour >=0
    minutes<60 
    minutes>=0
    seconds<60 
    seconds>=0
}

sig RelativeTime{
    validDays: set Day,
    hour: one Int,
    minutes: one Int,
    seconds: one Int
}{
    hour<25 
    hour>=0
    minutes<60 
    minutes>=0
    seconds<60 
    seconds>=0
}

sig Location{
    latitude: one Float,
    longitude: one Float
}

sig Store{
    commercialName: seq Char,
    longName: seq Char,
    Location: Location,
    opensAt: lone RelativeTime,
    closesAt: lone RelativeTime,
    twentyfour: one Bool
}

abstract sig Person {
    name: seq Char,
    surname: seq Char,
    fc: seq Char,
    customerId: seq Char
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
    duration: one Int,
    id: one String
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


pred isCustomer[p:Person]{
    p in CustomerDB.customers 
}
pred isStaff[p:Person]{
    p in StaffDB.staffMembers
}


run isCustomer for 7 Int
run isStaff for 7 Int