
/*******************************
	            DATA TYPE
********************************/
abstract sig Status{}
one sig Free extends Status{}
one sig Unavailable extends Status{}

sig integer{}
sig string{}

sig Location{
	street: one string ,
	number: one integer,
	ZIP: one integer,
	city: one string,
}


sig Date{
	day: one integer,
	month: one integer,
	year: one integer
}

sig DateOfEvent extends Date{
	time: one Time,
}

sig Time{
	hour: one integer,
	minute: one integer,
	second: one integer
}

abstract sig Type{}
one sig Autovehicle extends Type{}
one sig Minivan extends Type{}

/**********************************
	               ENTITIES
**********************************/
abstract sig  RegisteredUser{
	firstname: one string,
	lastname: one string,
	email: one string,
	address: one Location,
	username: one string,
	password: one string
}

sig Passenger extends RegisteredUser{
	history: set Ride,
	reservations: set Reservation,
}

sig TaxiDriver extends RegisteredUser{
	taxi: one Taxi,
	current_position: one Location,
	driving_license: one string,
	status: one Status
}

sig Taxi{
	ID: one integer,
	seats: one integer,
	type: one Type
}

sig Queue{
	head : lone TaxiDriver,
	tail: lone TaxiDriver,
	taxis: set TaxiDriver,
	zone: one Zone
}{#taxis>=0 }

sig Zone{
	locations: set Location,
	queue : one Queue
}{#locations>0}

sig Ride{
	passenger: one Passenger,
	driver: one TaxiDriver,
	pickupLocation: one Location,
	destination: one Location,
	startDateTime : one DateOfEvent,
	seats: one integer,
	payment: one string
}

sig Reservation{
	ride: lone Ride,
	passenger: one Passenger,
	pickupLocation: one Location,
	destination: one Location,
	reservationDateTime: one DateOfEvent,
	seats: one integer,
	payment: one string
}

/**********************************
	               FUNCTIONS
************************************/

fun getTaxiDriver[q:Queue]: one TaxiDriver {
	(q.taxis -q.head -q.tail)
} 


/**********************************
	                   FACTS
************************************/
fact EntitiesExistance{
	#Zone>1 
}
//No duplicate user
fact NoDuplicateUsers{
	no disj u,u1:RegisteredUser | (u.username=u1.username) or (u.email = u1.email)
}

//No taxi drivers with the same driving license
fact NoDuplicateLicense{
	no disj t,t1:TaxiDriver | (t.driving_license=t1.driving_license)
}

//No taxis with the same ID
fact NoDuplicateTaxiID{
	no disj t,t1 : Taxi | t.ID=t1.ID
}

//No taxi driver with the same taxi
fact NoTaxiDriverWithSameTaxi{
	no disj t,t1:TaxiDriver | t.taxi = t1.taxi
}

//If one zone contains one queue, then this queue is contained in that zone
fact ZonesQueuesAssociationIsUnique{
	all q:Queue, z:Zone | z=q.zone iff q=z.queue
}

//One location belongs to exactely one zone
fact ZoneStructure{
	no disj z,z1:Zone |
	(some loc:Location |
	(loc in z.locations) and (loc in z1.locations))
}

//All locations must belong to a zone
fact OneLocationOneZone{
	all loc:Location | one z:Zone | loc in z.locations
}

//No rides with the same date and time(hour,minute) coming from the same passenger 
fact NoDifferentRides{
	no disj r,r1: Ride | (r.passenger=r1.passenger) and (r.startDateTime=r1.startDateTime)
}

//No taxi driver in different queue
fact NoTaxiDriverInDifferentQueue{
	no t:TaxiDriver, q,q1:Queue | (t in q.taxis) and (t in q1.taxis) and(q != q1)
}

//Pickup location and destination in a ride and in a reservation should be different
fact PickupLocationDifferentFromDestination{
	all r:Ride | (r.pickupLocation != r.destination)
    all r:Reservation | (r.pickupLocation != r.destination)
}

//Unavailable taxi driver does not appear in any queue
fact NoUnavailableTaxiInQueues{
	all q:Queue, t:TaxiDriver | (t in (q.taxis)) => (t.status=Free)
}

//If a taxi's location belongs to a certain zone, then the taxi (if is available) must appear 
//in the queue of that zone
fact TaxiDriverLocation{
	all t:TaxiDriver, z:Zone | (t.status=Free) and (t.current_position in z.locations) => (t in z.queue.taxis)
}

//If the queue is empty there is no head nor tail
fact EmptyQueue{
	all q:Queue | (#q.taxis=0) implies ((#q.head=0) and (#q.tail=0))
}

//If the queue has one element head=tail
fact OneElementinQueue{
	all q:Queue |  (#q.taxis=1) implies ((q.head=q.tail) and (#q.head=1))
}

//If the queue has more then one element head!=tail
fact MoreElementinQueue{
	all q:Queue |  (#q.taxis>1) implies ((q.head!=q.tail) and (#q.head=1) and (#q.tail=1))
}

//Head and Tail are taxi that appears in the queue
fact TaxiDriverExistanceInQueue{
	all q:Queue | (#q.taxis>0) implies ((q.head in q.taxis) and (q.tail in q.taxis))
}

//All rides appear only in the history of their passenger
fact HistoryConstraint{
	all p:Passenger, r:Ride | (p=r.passenger) iff (r in p.history)
} 

//If a Reservation is not cancelled, it becomes a ride. 
//That ride should have the same attributes of Reservation except for the time.
fact ReservationToRide{
	all res:Reservation | (#res.ride=1) implies ((res.passenger=res.ride.passenger)
		and(res.pickupLocation=res.ride.pickupLocation)and(res.destination = res.ride.destination)
		and(res.reservationDateTime.day = res.ride.startDateTime.day) 
		and (res.reservationDateTime.month = res.ride.startDateTime.month)
		and(res.reservationDateTime.year = res.ride.startDateTime.year) 
		and (res.seats = res.ride.seats) and(res.payment = res.ride.payment))
}

//All reservations belong to only one passenger
fact NoReservationWithDifferentPassenger{
	all p:Passenger, r:Reservation | (p=r.passenger) iff (r in p.reservations)
} 

//there are no reservation that refer to the same ride
fact NoReservationWithSameRide{
	no disj r,r1:Reservation | r.ride = r1.ride
}

/**********************************
	                ASSERTIONS
************************************/

//If a queue  has at least one element, its head and tail must be a taxi between those elements
assert queueConsistency{
	all q:Queue |  (#q.taxis>0) implies ((#q.head=1) and (#q.tail=1) and 
		(q.head in q.taxis) and (q.tail in q.taxis))
}
check queueConsistency

//No zones with the same queue and no queues with the same zones
assert noDuplicateQueueOrZone{
	no disj z,z1: Zone | z.queue = z1.queue
	no  disj q,q1: Queue | q.zone = q1.zone
}
check noDuplicateQueueOrZone


assert addTaxi{
    //if a taxi is not in a queue, it can be added to it and it becomes the new tail of that queue
	all q,q1:Queue, t:TaxiDriver | 
	(!(t in q.taxis) and addTaxiDriverToQueue[q,q1,t] and #q.taxis>0) implies ((#q1.taxis = #q.taxis +1) and (q1.head = q.head) and (q1.tail = t))

    //if a taxi is added to a queue that has no taxis in it, both the head and the tail of that queue are updated
	all q,q1:Queue, t:TaxiDriver | 
	(!(t in q.taxis)and addTaxiDriverToQueue[q,q1,t] and #q.taxis=0) implies ((#q1.taxis = #q.taxis +1) and (q1.head = t) and (q1.tail = t))
}
check addTaxi


assert removeTaxi{
	//if a taxi is not in a queue, it can't be removed from it
	all q,q1:Queue, t:TaxiDriver | 
	!(t in q.taxis) and removeTaxiDriverFromQueue[q,q1,t]  implies (#q1.taxis = #q.taxis)

	//if a taxi is in a queue, it can be removed from it
	all q,q1:Queue, t:TaxiDriver | 
	(t in q.taxis) and removeTaxiDriverFromQueue[q,q1,t]  implies (#q1.taxis = #q.taxis -1)
	
	//if the head of a queue is removed from it, the head is updated and the tail remains the same
	all q,q1:Queue, t:TaxiDriver | (removeTaxiDriverFromQueue[q,q1,t]and (q.head=t and #q.taxis>2)) 
	implies ((q1.head in q.taxis) and !(q1.head = q.head)and (q1.tail = q.tail))
}
check removeTaxi

assert addRide{
	//a new ride can be added to a passenger's history if it is not already in it
	all p,p1:Passenger, r:Ride |
	(!(r in p.history) and addRideToHistory[p,p1,r]) implies (#p1.history = #p.history +1)

	//if a ride is already in a queue, it can't be added again
	all p,p1:Passenger, r:Ride |
	((r in p.history) and addRideToHistory[p,p1,r]) implies (#p1.history = #p.history)

}
check addRide

//if a reservation has not already become a ride, it can be cancelled from the system
assert cancellableReservation{
	 all p,p1:Passenger, r:Reservation |
	 (r in p.reservations and #r.ride=0 and cancelReservation[p,p1,r]) implies ((#p1.reservations=#p.reservations - 1) and !(r in p1.reservations)) 
}
check cancellableReservation

//if a reservation has already become a ride, it can be cancelled
assert uncancellableReservation{
	 all p,p1:Passenger, r:Reservation |
	 ((r in p.reservations) and #r.ride=1 and cancelReservation[p,p1,r]) implies ((#p1.reservations=#p.reservations) and (r in p1.reservations))
}
check uncancellableReservation


/**********************************
	                PREDICATES
************************************/
pred show{
	#Location >1
	#Zone>1
	#Queue>1
	#Ride>1
	#Reservation>1
	#TaxiDriver>1
	#Passenger>2

}
run show for 5

pred addTaxiDriverToQueue[q,q1:Queue, t:TaxiDriver] {
	!(t in q.taxis) implies (q1.taxis = q.taxis + t)
	(t in q.taxis) implies (q1.taxis = q.taxis)
	//Update head and tail
	(!(t in q.taxis) and #q.taxis>0) implies ((q1.head = q.head) and q1.tail = t)
		else (q1.head = t and q1.tail = t)
}
run addTaxiDriverToQueue for 8

pred removeTaxiDriverFromQueue[q,q1:Queue, t:TaxiDriver] {
	(t in q.taxis) implies (q1.taxis = q.taxis - t)
	!(t in q.taxis) implies (q1.taxis = q.taxis)
	//Update head and tail
	(q.head=t and #q.taxis>2) implies ((q1.head = q.getTaxiDriver) and (q1.tail = q.tail))
	(q.head=t and #q.taxis=2) implies ((q1.head = q.tail) and (q1.tail = q.tail))
	(q.head=t and #q.taxis=1) implies ((#q1.head = 0) and (#q1.tail=0))
	(t in q.taxis and q.head!=t and #q.taxis=2) implies ((q1.head = q.head) and (q1.tail=q.head))
	(t in q.taxis and q.head!=t and q.tail!=t and #q.taxis>2) implies ((q1.head = q.head) and (q1.tail=q.tail))
	(q.tail=t and #q.taxis>2) implies ((q1.head = q.head) and (q1.tail=q.getTaxiDriver))
}
run removeTaxiDriverFromQueue for 8

pred addRideToHistory[p,p1:Passenger, r:Ride]{
	(r in p.history) implies (p1.history=p.history)
	!(r in p.history) implies (p1.history=p.history +r)
}
run addRideToHistory for 8

pred addReservation[p,p1:Passenger, r:Reservation]{
    (r in p.reservations) implies (p1.reservations=p.reservations) 
	!(r in p.reservations) implies (p1.reservations=p.reservations +r)
}
run addReservation for 8

pred cancelReservation[p,p1:Passenger, r:Reservation]{
    (r in p.reservations and #r.ride=0) implies (p1.reservations=p.reservations - r) 
	//if the reservation doesn't exist or it has already become a ride, it is not cancelled
	(!(r in p.reservations) or #r.ride=1) implies (p1.reservations=p.reservations)
}
run cancelReservation for 8

