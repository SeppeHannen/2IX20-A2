/*
	Lock system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one lock and a configurable number of ships.

	This file contains:
	- process types for locks and ships that can be used as-is for the single lock case
	- a dummy specification of the main controller
	- initialization for the single-lock, single-ship case.
*/

/*
	To use weak fairness in a model with synchronous channels add -DNOREDUCE -DNFAIR = 
	<nr of processes> to the c compiler options.
*/

/*
	Syntax: 	&& (and), || (or), -> (implies), <-> (equivalent), ! (negation), 
			[] (always), <> (eventually), U (until).

*/

// The number of locks.
#define N	3
// The number of ships.
#define M	1
// The maximum number of ships immediately at either side of a lock.
#define MAX 2

// Type for direction of ship.
mtype:direction = { go_down, go_down_in_lock, go_up, go_up_in_lock, goal_reached };

// Type for water level.
mtype:level = { low_level, high_level };

// Type for lock side indication.
mtype:side = { low, high };

// Type for lock or slide indication.
mtype:comp = { door, slide }

// Type for door and slide position.
mtype:pos = { closed, open };

// Datatypes to store the status of the doors and slides of a lock.
typedef doorpairs_t {
	mtype:pos lower;
	mtype:pos higher;
}

typedef slides_t {
	mtype:pos lower;
	mtype:pos higher;
}

// Asynchronous channels to handle ship requests.
chan request_low = [M] of { bool, int, int };
chan request_high = [M] of { bool, int, int };

// Synchronous channels to indicate that a ship has seen that a particular pair
// of doors has opened.
chan observed_low[N] = [0] of { bool };
chan observed_high[N] = [0] of { bool };

// Status of the water level inside a lock.
mtype:level lock_water_level[N];

// Is there a ship currently in the lock?
bool lock_is_occupied[N];

// Status of the ships.
mtype:direction ship_status[M];

// Position of the ships.
byte ship_pos[M];

// Number of ships per position.
byte nr_of_ships_at_pos[N+1];

// Status and synchronous channels for doors.
doorpairs_t doors_status[N];
slides_t slide_status[N];
chan change_doors_pos[N] = [0] of { mtype:side };
chan doors_pos_changed[N] = [0] of { bool };
chan change_slide_pos[N] = [0] of { mtype:side };
chan slide_pos_changed[N] = [0] of { bool };

// Lock process type. It reacts to requests to open its doors and slides.
proctype lock(byte lockid) {
	do
	:: change_doors_pos[lockid]?low ->
		if
		:: doors_status[lockid].lower == closed -> doors_status[lockid].lower = open;
			lock_water_level[lockid] = low_level;
		:: doors_status[lockid].lower == open -> doors_status[lockid].lower = closed;
		fi;
		doors_pos_changed[lockid]!true;
	:: change_doors_pos[lockid]?high ->
		if
		:: doors_status[lockid].higher == closed -> doors_status[lockid].higher = open;
			if
			:: doors_status[lockid].lower == closed && slide_status[lockid].lower == closed ->
				lock_water_level[lockid] = high_level;
			:: doors_status[lockid].lower == open || slide_status[lockid].lower == open -> skip;
			fi;
		:: doors_status[lockid].higher == open -> doors_status[lockid].higher = closed;
		fi;
		doors_pos_changed[lockid]!true;
	:: change_slide_pos[lockid]?low ->
		if
		:: slide_status[lockid].lower == closed -> slide_status[lockid].lower = open;
			lock_water_level[lockid] = low_level;
		:: slide_status[lockid].lower == open -> slide_status[lockid].lower = closed;
		fi;
		change_slide_pos[lockid]!true;
	:: change_slide_pos[lockid]?high ->
		if
		:: slide_status[lockid].higher == closed -> slide_status[lockid].higher = open;
			if
			:: doors_status[lockid].lower == closed && slide_status[lockid].lower == closed ->
				lock_water_level[lockid] = high_level;
			:: doors_status[lockid].lower == open || slide_status[lockid].lower == open -> skip;
			fi;
		:: slide_status[lockid].higher == open -> slide_status[lockid].higher = closed;
		fi;
		change_slide_pos[lockid]!true;
	od;
}

// Ship process type. Based on its direction and position, it makes requests to open doors,
// and moves when possible.
proctype ship(byte shipid) {
	do
	// Ship wants to go down and is not at the end of the system of locks.
	:: ship_status[shipid] == go_down && ship_pos[shipid] != 0 ->
		do
		:: doors_status[ship_pos[shipid]].higher == closed ->
			atomic{ request_high!true, ship_pos[shipid], shipid; 
				if
				:: !lock_is_occupied[ship_pos[shipid]] ->
						ship_status[shipid] = go_down_in_lock;
						lock_is_occupied[ship_pos[shipid]] = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_high[shipid]!true, shipid;
						break;
				:: lock_is_occupied[ship_pos[shipid]] ->
						observed_high[shipid]!true, shipid;
				fi; }
		:: atomic { doors_status[ship_pos[shipid]-1].higher == open &&
			!lock_is_occupied[ship_pos[shipid]] ->
				ship_status[shipid] = go_down_in_lock;
				lock_is_occupied[ship_pos[shipid]] = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	// Ship wants to go down in lock.
	:: ship_status[shipid] == go_down_in_lock ->
		do
		// The lower doors are closed.
		:: doors_status[ship_pos[shipid]].lower == closed ->
			request_low!true, ship_pos[shipid], shipid;
			atomic { doors_status[ship_pos[shipid]].lower == open ->
				if
				// The lower doors are open and there is space to exit the lock, or we are the end of the system of locks.
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
					|| ship_pos[shipid]-1 == 0) ->
						ship_status[shipid] = go_down;
						lock_is_occupied[ship_pos[shipid]] = false;
						ship_pos[shipid]--;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_low[shipid]!true;
						break;
				// The lower doors are open and there is no space to exit the lock.
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] == MAX
					&& ship_pos[shipid]-1 != 0) ->
						observed_low[shipid]!true;
				fi; }
		// The lower doors are open and there is room for the ship to exit the lock, or we are the end of the system of locks.
		:: atomic { doors_status[ship_pos[shipid]].lower == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
			|| ship_pos[shipid]-1 == 0) ->
				ship_status[shipid] = go_down;
				lock_is_occupied[ship_pos[shipid]] = false;
				ship_pos[shipid]--;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	// Ship wants to go up and is not at the end of the system of locks.
	:: ship_status[shipid] == go_up && ship_pos[shipid] != N ->
		do
		// The lower doors are closed.
		:: doors_status[ship_pos[shipid] + 1].lower == closed ->
			request_low!true, ship_pos[shipid] + 1, shipid;
			atomic { doors_status[ship_pos[shipid]].lower == open ->
				if
				// The lower doors are open and the lock has space.
				:: !lock_is_occupied[ship_pos[shipid] + 1] ->
						ship_status[shipid] = go_up_in_lock;
						lock_is_occupied[ship_pos[shipid] + 1] = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_low[shipid]!true;
						break;
				// The lower doors are open but the lock has no space.
				:: lock_is_occupied[ship_pos[shipid] + 1] ->
						observed_low[shipid]!true;
				fi; }
		:: atomic { doors_status[ship_pos[shipid]].lower == open &&
			!lock_is_occupied[ship_pos[shipid]] ->
				ship_status[shipid] = go_up_in_lock;
				lock_is_occupied[ship_pos[shipid] + 1] = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	// Ship wants to go up in lock.
	:: ship_status[shipid] == go_up_in_lock ->
		do
		// The higher doors are closed
		:: doors_status[ship_pos[shipid] + 1].higher == closed ->
			request_high!true, ship_pos[shipid] + 1, shipid;	
			atomic { doors_status[ship_pos[shipid] + 1].higher == open ->
				if
				// The higher doors are open and there is room to exit the lock.
				:: (nr_of_ships_at_pos[ship_pos[shipid] + 1] < MAX
					|| ship_pos[shipid] + 1 == N) ->
						ship_status[shipid] = go_up;
						lock_is_occupied[ship_pos[shipid] + 1] = false;
						ship_pos[shipid]++;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_high[shipid]!true;
						break;
				// The higher doors are open but there is no room to exit the lock.
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] == MAX
					&& ship_pos[shipid]+1 != N) ->
						observed_high[ship_pos[shipid] + 1]!true;
				fi; }
		// The higher doors are open and there is room to exit the lock.
		:: atomic { doors_status[ship_pos[shipid] + 1].higher == open &&
			(nr_of_ships_at_pos[ship_pos[shipid] + 1] < MAX
			|| ship_pos[shipid]+1 == N) ->
				ship_status[shipid] = go_up;
				lock_is_occupied[ship_pos[shipid] + 1] = false;
				ship_pos[shipid]++;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	// When the ship reaches its goal, update the status.
	:: ship_status[shipid] == go_down && ship_pos[shipid] == 0 ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_up;
	:: ship_status[shipid] == go_up && ship_pos[shipid] == N ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_down;
	od;
}

// DUMMY main control process type. Remodel it to control the lock system and handle
// requests of ships!
proctype main_control() {
	bool low_req;
	bool high_req;
	int low_shipid;
	int high_shipid;
	int low_lockid
	int high_lockid;
	do

	// Receive a request 
	:: request_low?low_req, low_shipid, low_lockid;
		low_req ->
		if
		:: lock_water_level[low_lockid] == low_level ->
			if
			:: doors_status[low_lockid].lower == closed ->
				if
				:: doors_status[low_lockid].higher == closed ->
					change_doors_pos[low_lockid]!low; doors_pos_changed[low_lockid]?true;
				:: doors_status[low_lockid].higher == open -> 
					change_doors_pos[low_lockid]!high; doors_pos_changed[low_lockid]?true;
					change_doors_pos[low_lockid]!low; doors_pos_changed[low_lockid]?true;
				fi;
			:: doors_status[low_lockid].lower == open -> skip;
			fi;
		:: lock_water_level[low_lockid] == high_level ->
			if
			:: doors_status[low_lockid].lower == closed ->
				if
				:: doors_status[low_lockid].higher == open ->
					change_doors_pos[low_lockid]!high; doors_pos_changed[low_lockid]?true;
				:: doors_status[low_lockid].higher == closed -> skip;
				fi;

				if
				:: slide_status[low_lockid].higher == open ->
					change_slide_pos[low_lockid]!high; change_slide_pos[low_lockid]?true;
				:: slide_status[low_lockid].higher == closed -> skip;
				fi;

				if
				:: slide_status[low_lockid].lower == closed ->
					change_slide_pos[low_lockid]!low; change_slide_pos[low_lockid]?true;
				:: slide_status[low_lockid].lower == open -> skip;
				fi;
				change_doors_pos[low_lockid]!low; doors_pos_changed[low_lockid]?true;
			:: doors_status[low_lockid].lower == open -> skip;
			fi;
		fi;

		observed_low[low_shipid]?true;


	:: request_high?high_req, high_shipid, high_lockid;
	high_req ->
		if
		:: lock_water_level[high_lockid] == high_level ->
			if
			:: doors_status[high_lockid].higher== closed ->
				if
				:: doors_status[high_lockid].lower== closed ->
					change_doors_pos[high_lockid]!high; doors_pos_changed[high_lockid]?true;
				:: doors_status[high_lockid].lower == open -> 
					change_doors_pos[high_lockid]!low; doors_pos_changed[high_lockid]?true;
					change_doors_pos[high_lockid]!high; doors_pos_changed[high_lockid]?true;
				fi;
			:: doors_status[high_lockid].higher == open -> skip;
			fi;
		:: lock_water_level[high_lockid] == low_level ->
			if
			:: doors_status[high_lockid].higher == closed ->
				if
				:: doors_status[high_lockid].lower == open ->
					change_doors_pos[high_lockid]!low; doors_pos_changed[high_lockid]?true;
				:: doors_status[high_lockid].lower == closed -> skip;
				fi;

				if
				:: slide_status[high_lockid].lower == open ->
					change_slide_pos[high_lockid]!low; change_slide_pos[high_lockid]?true;
				:: slide_status[high_lockid].lower == closed -> skip;
				fi;

				if
				:: slide_status[high_lockid].higher == closed ->
					change_slide_pos[high_lockid]!high; change_slide_pos[high_lockid]?true;
				:: slide_status[high_lockid].higher == open -> skip;
				fi;
				change_doors_pos[high_lockid]!high; doors_pos_changed[high_lockid]?true;
			:: doors_status[high_lockid].higher == open -> skip;
			fi;
		fi;

		observed_high[high_shipid]?true;
	od;
}

proctype monitor() {
	atomic {

	// A ship never leaves the system of locks (example).
	assert(0 <= ship_pos[0] && ship_pos[0] <= N);

	int lock_nr = 0;

	do 
		:: lock_nr < N ->
			// (a) The lower pairs of doors and the higher pairs of doors are never simultaneously open.
			assert(!((doors_status[lock_nr].lower == open) && (doors_status[lock_nr].higher == open)));

			// (b1) When the lower pair of doors is open, the higher slide is closed.
			//assert((doors_status.lower == open) -> (slide_status.higher == closed));
			assert(!(doors_status[lock_nr].lower == open) || (slide_status[lock_nr].higher == closed));

			// (b2) When the higher pair of doors is open, the lower slide is closed.
			//assert(doors_status.higher == open -> slide_status.lower == closed);
			assert(!(doors_status[lock_nr].higher == open) || (slide_status[lock_nr].lower == closed));

			// (c1) The lower pair of doors is only open when the water level in the lock is low.
			//assert(doors_status.lower == open -> lock_water_level == low_level);
			assert(!(doors_status[lock_nr].lower == open) || (lock_water_level[lock_nr] == low_level));

			// (c2) The higher pair of doors is only open when the water level in the lock is high.
			//assert(doors_status.higher == open -> lock_water_level == high_level);
			assert(!(doors_status[lock_nr].higher == open) || (lock_water_level[lock_nr] == high_level));

			lock_nr++;
		:: lock_nr == N -> 
			break;
	od;
	}
}

// LTL Formulas for other requirements:

	// (d1) Always if a ship requests the lower pair of doors to open and its status is go_up, 
	// the ship will eventually be inside the lock.
	// ltl d1 {[](((len(request_low) > 0) && (ship_status[0] == go_up)) -> <>(ship_status[0] == go_up_in_lock)) }

	// (d2) Always if a ship requests the higher pair of doors to open and its status is go_down, 
	// the ship will eventually be inside the lock.
	// ltl d2 {[](((len(request_high) > 0) && (ship_status[0] == go_up)) -> <>(ship_status[0] == go_up_in_lock)) }

	// (test1) The single-lock model is such that always eventually 
	// a ship requests to open the lower doors.
	// ltl test1 {[](<>(len(request_low) > 0))}

	// (test2) The single-lock model is such that always eventually 
	// a ship requests to open the higher doors.
	// ltl test2 {[](<>(len(request_high) > 0))}

	// (test3) The single-lock model is such that always eventually, 
	// the water level in the lock will be high
	// ltl test3 {[](<>(lock_water_level == high))}

	// (test4) The single-lock model is such that always eventually, 
	// the water level in the lock will be low
	// ltl test4 {[](<>(lock_water_level == low))}


// Initial process that instantiates all other processes and creates
// the initial lock and ship situation.
init {
	byte proc;
	atomic {
		run monitor();
		run main_control();
		// In the code below, the individual locks are initialised.
		// The assumption here is that N == 1. When generalising the model for
		// multiple locks, make sure that the do-statement is altered!
		proc = 0;
		do
		:: proc < N ->
			doors_status[proc].lower = closed;
			doors_status[proc].higher = closed;
			slide_status[proc].lower = closed;
			slide_status[proc].higher = closed;
			lock_water_level[proc] = high_level;
			lock_is_occupied[proc] = false;
			run lock(proc);
			proc++;
		:: proc == N -> break;
		od;
		// In the code below, the individual ship positions and directions
		// are initialised. Expand this when more ships should be added.
		proc = 0;
		do
		:: proc == 0 -> ship_status[proc] = go_up; ship_pos[proc] = 0;
			run ship(proc); proc++;
		:: proc > 0 && proc < M -> ship_status[proc] = go_up; ship_pos[proc] = 0;
			run ship(proc); proc++;
		:: proc == M -> break;
		od;
		// Do not change the code below! It derives the number of ships per
		// position from the positions of the individual ships.
		proc = 0;
		do
		:: proc < M -> nr_of_ships_at_pos[ship_pos[proc]]++; proc++;
		:: else -> break;
		od;
	}
}
