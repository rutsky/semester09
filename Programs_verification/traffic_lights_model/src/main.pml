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
#define N_TRAFFIC_LIGHTS  4

/* Number of intersections */
#define N_INTERSECTIONS 5

#define INVALID_TL_ID  255

/*** cut here ***/

/* Car object */
mtype = { CAR };

/* Cars waiting sign for each traffic light */
chan carsWaiting[N_TRAFFIC_LIGHTS] = [1] of { mtype };

/* Cars generator process */
proctype CarsGenerator()
{
  byte tlId;
  bit isExit;
  
  isExit = false;

endCG:
  do
  :: isExit ->
    break;
  :: else ->
    /* Generate car (probably) */
  
    tlId = 0;
    do
    :: (tlId < N_TRAFFIC_LIGHTS) ->
      if
      :: true ->
        /* Generate car */
        carsWaiting[tlId] ! CAR;
        break;
      :: true
        /* Skip car generation for current traffic light */
      fi;
      tlId++;
    :: else ->
      /* No cars generated, exiting */
      isExit = true;
      break;
    od;
  od
}

/*** cut here ***/

/* Manager messages */
mtype = { LOCK, INT, RELEASE };

/* Intersections lock/release requests queue.
 * Message contains requestee traffic light identifier.
 */
chan intersectionLockRequests[N_INTERSECTIONS] = [N_TRAFFIC_LIGHTS] of { mtype, byte };
chan intersectionLockGranted[N_TRAFFIC_LIGHTS] = [0] of { mtype };
chan intersectionReleaseRequests[N_INTERSECTIONS] = [0] of { mtype };

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
    intersectionReleaseRequests[intId] ? RELEASE;
  od;
}

/*** cut here ***/

/* Traffic lights states */
mtype = { RED, GREEN };

/* Traffic light state */
mtype tlColor[N_TRAFFIC_LIGHTS];

/* Main traffic light process */
proctype TrafficLight( byte initTlId )
{
  byte tlId;
  
  tlId = initTlId;

  assert(tlId != INVALID_TL_ID);
  assert(tlColor[tlId] == RED);

endTL:
  do
  :: carsWaiting[tlId] ? [CAR] ->
    /* Cars in queue */
  
    /* Lock dependent intersections */
    /* Note: another copy of diagram above.
     *
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
    atomic 
    {
      printf("MSC: Traffic light #%d: GREEN\n", tlId);
      tlColor[tlId] = GREEN;
      
      /* Pass car */
      /* Note: atomic for easier claim construction */
      printf("MSC: Traffix light #%d: pass cars\n", tlId);
      carsWaiting[tlId] ? CAR;
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
      unlockIntersection(0);
      unlockIntersection(1);
      unlockIntersection(2);
    :: tlId == WE ->
      unlockIntersection(0);
      unlockIntersection(3);
    :: tlId == ES ->
      unlockIntersection(2);
      unlockIntersection(3);
      unlockIntersection(4);
    :: tlId == NE ->
      unlockIntersection(1);
      unlockIntersection(4);
    fi;
  od;
}

/*** cut here ***/

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
    run CarsGenerator();
  }
}

/*** cut here ***/

/*
 * Correctness requirements.
 */

  /* Note: another copy of diagram above.
   *
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

/*
 * always      <=>  []
 * eventually  <=>  <>
 */

/* Safety: Intersecting roads traffic light both never has GREEN state */
ltl safe_green_01 { always (!(tlColor[0] == GREEN && tlColor[1] == GREEN)) }
ltl safe_green_02 { always (!(tlColor[0] == GREEN && tlColor[2] == GREEN)) }
ltl safe_green_03 { always (!(tlColor[0] == GREEN && tlColor[3] == GREEN)) }
ltl safe_green_13 { always (!(tlColor[1] == GREEN && tlColor[3] == GREEN)) }
ltl safe_green_23 { always (!(tlColor[2] == GREEN && tlColor[3] == GREEN)) }

/* Liveness: If cars wait on traffic light, then in future traffic light
 * became GREEN */
ltl car_will_pass_0 { always ((len(carsWaiting[0]) > 0) -> eventually (tlColor[0] == GREEN)) }
ltl car_will_pass_1 { always ((len(carsWaiting[1]) > 0) -> eventually (tlColor[1] == GREEN)) }
ltl car_will_pass_2 { always ((len(carsWaiting[2]) > 0) -> eventually (tlColor[2] == GREEN)) }
ltl car_will_pass_3 { always ((len(carsWaiting[3]) > 0) -> eventually (tlColor[3] == GREEN)) }
