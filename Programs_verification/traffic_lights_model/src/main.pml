/*
 *  This file is part of traffic lights model development and verification.
 *
 *  Copyright (C) 2010  Vladimir Rutsky <altsysrq@gmail.com>
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

  /* Variant 9-13:
   * SN, WE, NE, ES.
   */
  /*
   *               N
   *           2
   *           |       ^
   *           |       |
   *           |     --2-------3
   *            \   /  |
   *  W           4    |          E
   *            /   \  |
   *           /     --1------>
   *           |       |
   *    1 -----3-------0------>
   *           |       |
   *           v       |
   *                   0
   *               S
   *
   */

#define SN 0
#define WE 1
#define NE 2
#define ES 3

/* Number of traffic lights */
#define N_TRAFFIC_LIGHTS 4

/* Number of intersections */
#define N_INTERSECTIONS  5

/* Car object */
mtype = { CAR };

/* Cars waiting sign for each traffic light */
chan carsWaiting[N_TRAFFIC_LIGHTS] = [1] of { mtype };

proctype LineTrafficGenerator( byte initTlId )
{
  byte tlId;
  
  tlId = initTlId;
  
  do
  :: carsWaiting[tlId] ! CAR;
  od
}

/* Manager messages */
mtype = { LOCK, INT, RELEASE };

/* Intersections lock/release requests queue.
 * Message contains requestee traffic light identifier.
 */
chan intersectionLockRequests[N_INTERSECTIONS] = 
  [N_TRAFFIC_LIGHTS] of { mtype, byte };
chan intersectionLockGranted[N_TRAFFIC_LIGHTS] = 
  [0] of { mtype };
chan intersectionReleaseRequests[N_INTERSECTIONS] = 
  [0] of { mtype };

/* Macro for obtaining intersection resource */
#define lockIntersection( intId, tlId )   \
  intersectionLockRequests[intId] ! LOCK(tlId); \
  intersectionLockGranted[tlId] ? INT

/* Macro for releasing intersection resource */
#define unlockIntersection( intId ) \
  intersectionReleaseRequests[intId] ! RELEASE

/* Intersection resource manager */
proctype Intersection( byte initIntId )
{
  byte intId, tlId;

  intId = initIntId;

endInt:
  do
  :: intersectionLockRequests[intId] ? LOCK(tlId) ->
    /* Handle request */
    intersectionLockGranted[tlId] ! INT;

    /* Wait for release */
  progressGiveIntersection:
    intersectionReleaseRequests[intId] ? RELEASE;
  od;
}

/* Traffic lights states */
mtype = { RED, GREEN };

/* Traffic light state */
mtype tlColor[N_TRAFFIC_LIGHTS];

/* Main traffic light process */
proctype TrafficLight( byte initTlId )
{
  byte tlId;
  
  tlId = initTlId;

  assert(tlColor[tlId] == RED);

endTL:
  do
  :: carsWaiting[tlId] ? [CAR] ->
    /* Cars in queue */
  
    /* Lock dependent intersections */
    if
    :: tlId == SN ->
      lockIntersection(0, tlId);
      lockIntersection(1, tlId);
      lockIntersection(2, tlId);
    :: tlId == WE ->
      lockIntersection(0, tlId);
      lockIntersection(3, tlId);
    :: tlId == ES ->
      lockIntersection(2, tlId);
      lockIntersection(3, tlId);
      lockIntersection(4, tlId);
    :: tlId == NE ->
      lockIntersection(1, tlId);
      lockIntersection(4, tlId);
    fi;
    
    /* Allow passing */
  progressPassCar:
    atomic 
    {
      printf("MSC: Traffic light #%d: GREEN\n", tlId);
      tlColor[tlId] = GREEN;
      
      /* Pass car */
      /* Note: atomic for easier claim construction */
      carsWaiting[tlId] ? CAR;
      printf("MSC: Traffix light #%d: pass cars\n", tlId);
    };
    
    /* Forbid passing */
    atomic
    {
      printf("MSC: Traffic light #%d: RED\n", tlId);
      tlColor[tlId] = RED;
    };
    
    /* Release dependent intersections */
    if
    :: tlId == SN ->
      unlockIntersection(2);
      unlockIntersection(1);
      unlockIntersection(0);
    :: tlId == WE ->
      unlockIntersection(3);
      unlockIntersection(0);
    :: tlId == ES ->
      unlockIntersection(4);
      unlockIntersection(3);
      unlockIntersection(2);
    :: tlId == NE ->
      unlockIntersection(4);
      unlockIntersection(1);
    fi;
  od;
}

/* The main model function */
init
{
  byte tlId, intId;
  
  /* Reset traffic lights colors */
  tlId = 0;
  do
  :: tlId < N_TRAFFIC_LIGHTS ->
    tlColor[tlId] = RED;
    tlId++;
  :: else ->
    break;
  od;
  
  atomic
  {
    /* Start intersection managers processes */
    intId = 0;
    do
    :: intId < N_INTERSECTIONS ->
      run Intersection(intId);
      intId++;
    :: else ->
      break;
    od;
  
    /* Start traffic lights processes */
    tlId = 0;
    do
    :: tlId < N_TRAFFIC_LIGHTS ->
      run TrafficLight(tlId);
      tlId++;
    :: else ->
      break;
    od;
  
    /* Start cars generator process */
    /*run CarsGenerator();*/
    tlId = 0;
    do
    :: tlId < N_TRAFFIC_LIGHTS ->
      run LineTrafficGenerator(tlId);
      tlId++;
    :: else ->
      break;
    od;
  }
}

/*
 * Correctness requirements.
 */

/* Car crash accident definition */
#define accident_01 (tlColor[0] == GREEN && tlColor[1] == GREEN)
#define accident_02 (tlColor[0] == GREEN && tlColor[2] == GREEN)
#define accident_03 (tlColor[0] == GREEN && tlColor[3] == GREEN)
#define accident_13 (tlColor[1] == GREEN && tlColor[3] == GREEN)
#define accident_23 (tlColor[2] == GREEN && tlColor[3] == GREEN)

/* Car waiting at traffic light definition */
#define car_waiting_0 (len(carsWaiting[0]) > 0)
#define car_waiting_1 (len(carsWaiting[1]) > 0)
#define car_waiting_2 (len(carsWaiting[2]) > 0)
#define car_waiting_3 (len(carsWaiting[3]) > 0)

/* Traffic light is green definition */
#define tl_green_0 (tlColor[0] == GREEN)
#define tl_green_1 (tlColor[1] == GREEN)
#define tl_green_2 (tlColor[2] == GREEN)
#define tl_green_3 (tlColor[3] == GREEN)

/* Safety: Intersecting roads traffic light both never has GREEN state */
/*
 * [] (!accident_01)
 * [] (!accident_02)
 * [] (!accident_03)
 * [] (!accident_13)
 * [] (!accident_23)
 */

/* Liveness: If cars wait on traffic light, then in future traffic light
 * became GREEN */
/*
 * [] (car_waiting_0 -> <> tl_green_0)
 * [] (car_waiting_1 -> <> tl_green_1)
 * [] (car_waiting_2 -> <> tl_green_2)
 * [] (car_waiting_3 -> <> tl_green_3)
 */
