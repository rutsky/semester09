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

/* Number of intersections */
#define N_INTERSECTIONS 5

/* Number of traffic lights */
#define N_TRAFFIC_LIGHTS  4
/* Maximum number of cars in signle traffig light queue */
#define CARS_QUEUE_LEN   1

#define INVALID_INT_ID 255
#define INVALID_TL_ID  255

mtype = { RED, GREEN, CAR };

/* Current owner of intersection resource */
byte intersectionOwner[N_INTERSECTIONS];

/* Macro for obtaining intersection resource */
#define lockIntersection( intId, tlId )               \
  do                                                  \
  :: true -> atomic {                                 \
      if                                              \
      :: intersectionOwner[intId] == INVALID_TL_ID -> \
        intersectionOwner[intId] = tlId;              \
        break                                         \
      :: else ->                                      \
        skip                                          \
      fi                                              \
    }                                                 \
  od

/* Macro for releasing intersection resource */
#define unlockIntersection( intId, tlId )             \
  assert(intersectionOwner[intId] == tlId);           \
  intersectionOwner[intId] = INVALID_TL_ID

/* Queue of cars for each traffic light */
chan cars[N_TRAFFIC_LIGHTS] = [CARS_QUEUE_LEN] of { mtype };

/* Traffic light state */
mtype tlColor[N_TRAFFIC_LIGHTS];

/* Main traffic light process */
proctype TrafficLight( byte initTlId )
{
  byte tlId;
  tlId = initTlId;

  assert(tlId != INVALID_TL_ID);
  assert(tlColor[tlId] == RED);
  
  do
  :: cars[tlId] ? [CAR] ->
    /* Cars in queue */
  
    /* Lock dependent intersections */
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
    };
    
    /* Pass car */
    atomic
    {
      printf("MSC: Traffix light #%d: pass car\n", tlId);
      cars[tlId] ? CAR;
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
      unlockIntersection(0, tlId);
      unlockIntersection(1, tlId);
      unlockIntersection(2, tlId);
    :: tlId == WE ->
      unlockIntersection(0, tlId);
      unlockIntersection(3, tlId);
    :: tlId == ES ->
      unlockIntersection(2, tlId);
      unlockIntersection(3, tlId);
      unlockIntersection(4, tlId);
    :: tlId == NE ->
      unlockIntersection(1, tlId);
      unlockIntersection(4, tlId);
    fi
  od
}

/* Cars generator process */
proctype CarsGenerator()
{
  byte tlId;

  do
  :: true ->
    /* Generate car (probably) */
  
    tlId = 0;
    do
    :: (tlId < N_TRAFFIC_LIGHTS) ->
      if
      :: nfull(cars[tlId]) ->
        /* Generate car and exit cycle */
        cars[tlId] ! CAR;
      :: true ->
        /* Skip car generation for current traffic light */
        skip
      fi;
      tlId++;
    :: else ->
      break;
    od;

  :: true ->
    /* Nondeterministically stop car generation */
    break;
  od
}

/* The main model function */
init
{
  byte tlId, intId, intIdx;
  
  /* Reset intersection owners */
  intId = 0;
  do
  :: intId < N_INTERSECTIONS ->
    intersectionOwner[intId] = INVALID_TL_ID;
    intId++;
  :: else ->
    break;
  od;
  
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

/* Safety: Intersecting roads traffic light both never has GREEN state */
                /* [] */
ltl safe_green { always !(tlColor[0] == GREEN && tlColor[1] == GREEN) &&
                        !(tlColor[0] == GREEN && tlColor[2] == GREEN) &&
                        !(tlColor[0] == GREEN && tlColor[3] == GREEN) &&
                        !(tlColor[1] == GREEN && tlColor[3] == GREEN) &&
                        !(tlColor[2] == GREEN && tlColor[3] == GREEN) }

/* Liveness: If cars wait on traffic light, then in future traffic light
 * became GREEN */
//ltl car_will_pass { always }