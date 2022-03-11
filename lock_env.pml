/*
	Lock system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one lock and a configurable number of ships.

	This file contains:
	- process types for locks and ships that can be used as-is for the single lock case
	- a dummy specification of the main controller
	- initialization for the single-lock, single-ship case.
*/

// The number of locks.
#define N	1
// The number of ships.
#define M	1
// The maximum number of ships immediately at either side of a lock.
#define MAX 2

// LTL formulas to be verified
// Formula p1 holds if the first ship can always eventually enter the lock when going up.
//ltl p1 { []<> (ship_status[0] == go_up_in_lock) } /*  */

// Type for direction of ship.
mtype:direction = { go_down, go_down_in_lock, go_up, go_up_in_lock, goal_reached };

// Type for water level.
mtype:level = { low_level, high_level };

// Type for lock side indication.
mtype:side = { low, high };

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
chan request_low = [M] of { bool };
chan request_high = [M] of { bool };
// Synchronous channels to indicate that a ship has seen that a particular pair
// of doors has opened.
chan observed_low[N] = [0] of { bool };
chan observed_high[N] = [0] of { bool };

// Status of the water level inside a lock.
mtype:level lock_water_level;
// Is there a ship currently in the lock?
bool lock_is_occupied;

// Status of the ships.
mtype:direction ship_status[M];
// Position of the ships.
byte ship_pos[M];
// Number of ships per position.
byte nr_of_ships_at_pos[N+1];

// Status and synchronous channels for doors.
doorpairs_t doors_status;
slides_t slide_status;
chan change_doors_pos = [0] of { mtype:side };
chan doors_pos_changed = [0] of { bool };
chan change_slide_pos = [0] of { mtype:side };
chan slide_pos_changed = [0] of { bool };

// Lock process type. It reacts to requests to open its doors and slides.
proctype lock(byte lockid) {
	do
	:: change_doors_pos?low ->
		if
		:: doors_status.lower == closed -> doors_status.lower = open;
			lock_water_level = low_level;
		:: doors_status.lower == open -> doors_status.lower = closed;
		fi;
		doors_pos_changed!true;
	:: change_doors_pos?high ->
		if
		:: doors_status.higher == closed -> doors_status.higher = open;
			if
			:: doors_status.lower == closed && slide_status.lower == closed ->
				lock_water_level = high_level;
			:: doors_status.lower == open || slide_status.lower == open -> skip;
			fi;
		:: doors_status.higher == open -> doors_status.higher = closed;
		fi;
		doors_pos_changed!true;
	:: change_slide_pos?low ->
		if
		:: slide_status.lower == closed -> slide_status.lower = open;
			lock_water_level = low_level;
		:: slide_status.lower == open -> slide_status.lower = closed;
		fi;
		slide_pos_changed!true;
	:: change_slide_pos?high ->
		if
		:: slide_status.higher == closed -> slide_status.higher = open;
			if
			:: doors_status.lower == closed && slide_status.lower == closed ->
				lock_water_level = high_level;
			:: doors_status.lower == open || slide_status.lower == open -> skip;
			fi;
		:: slide_status.higher == open -> slide_status.higher = closed;
		fi;
		slide_pos_changed!true;
	od;
}

// Ship process type. Based on its direction and position, it makes requests to open doors,
// and moves when possible.
proctype ship(byte shipid) {
	do
	:: ship_status[shipid] == go_down && ship_pos[shipid] != 0 ->
		do
		:: doors_status.higher == closed ->
			request_high!true;
			atomic { doors_status.higher == open ->
				if
				:: !lock_is_occupied ->
						ship_status[shipid] = go_down_in_lock;
						lock_is_occupied = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_high[0]!true;
						break;
				:: lock_is_occupied ->
						observed_high[0]!true;
				fi; }
		:: atomic { doors_status.higher == open &&
			!lock_is_occupied ->
				ship_status[shipid] = go_down_in_lock;
				lock_is_occupied = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	:: ship_status[shipid] == go_down_in_lock ->
		do
		:: doors_status.lower == closed ->
			request_low!true;
			atomic { doors_status.lower == open ->
				if
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
					|| ship_pos[shipid]-1 == 0) ->
						ship_status[shipid] = go_down;
						lock_is_occupied = false;
						ship_pos[shipid]--;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_low[0]!true;
						break;
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] == MAX
					&& ship_pos[shipid]-1 != 0) ->
						observed_low[0]!true;
				fi; }
		:: atomic { doors_status.lower == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
			|| ship_pos[shipid]-1 == 0) ->
				ship_status[shipid] = go_down;
				lock_is_occupied = false;
				ship_pos[shipid]--;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	:: ship_status[shipid] == go_up && ship_pos[shipid] != N ->
		do
		:: doors_status.lower == closed ->
			request_low!true;
			atomic { doors_status.lower == open ->
				if
				:: !lock_is_occupied ->
						ship_status[shipid] = go_up_in_lock;
						lock_is_occupied = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_low[0]!true;
						break;
				:: lock_is_occupied ->
						observed_low[0]!true;
				fi; }
		:: atomic { doors_status.lower == open &&
			!lock_is_occupied ->
				ship_status[shipid] = go_up_in_lock;
				lock_is_occupied = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	:: ship_status[shipid] == go_up_in_lock ->
		do
		:: doors_status.higher == closed ->
			request_high!true;
			atomic { doors_status.higher == open ->
				if
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
					|| ship_pos[shipid]+1 == N) ->
						ship_status[shipid] = go_up;
						lock_is_occupied = false;
						ship_pos[shipid]++;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_high[0]!true;
						break;
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] == MAX
					&& ship_pos[shipid]+1 != N) ->
						observed_high[0]!true;
				fi; }
		:: atomic { doors_status.higher == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
			|| ship_pos[shipid]+1 == N) ->
				ship_status[shipid] = go_up;
				lock_is_occupied = false;
				ship_pos[shipid]++;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	:: ship_status[shipid] == go_down && ship_pos[shipid] == 0 ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_up;
	:: ship_status[shipid] == go_up && ship_pos[shipid] == N ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_down;
	od;
}

// DUMMY main control process type. Remodel it to control the lock system and handle
// requests of ships!
proctype main_control() {
	do
	:: request_low?true ->
		if
		:: doors_status.lower == closed ->
			change_doors_pos!low; doors_pos_changed?true;
		:: doors_status.lower == open -> skip;
		fi;
		observed_low[0]?true;
	:: request_high?true ->
		if
		:: doors_status.higher == closed ->
			change_doors_pos!high; doors_pos_changed?true;
		:: doors_status.higher == open -> skip;
		fi;
		observed_high[0]?true;
	od;
}

proctype monitor() {
	// an example assertion.
	assert(0 <= ship_pos[0] && ship_pos[0] <= N);
}

// Initial process that instantiates all other processes and creates
// the initial lock and ship situation.
init {
	byte proc;
	atomic {
		//run monitor();
		run main_control();
		// In the code below, the individual locks are initialised.
		// The assumption here is that N == 1. When generalising the model for
		// multiple locks, make sure that the do-statement is altered!
		proc = 0;
		do
		:: proc < N ->
			doors_status.lower = closed;
			doors_status.higher = closed;
			slide_status.lower = closed;
			slide_status.higher = closed;
			lock_water_level = high_level;
			lock_is_occupied = false;
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
		:: proc > 0 && proc < M -> proc++;
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
