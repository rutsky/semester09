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

/* Number of intersections */
#define N_INTERSECTIONS          5
#define N_INTERSECTIONS_PLUS_ONE 6

/* Number of traffic lights */
#define N_TRAFFIC_LIGHTS  4
/* Maximum number of cars in signle traffig light queue */
#define CARS_QUEUE_LEN   1

/* Minumum number of cars that will be generated (useful for debug) */
#define MINIMUM_GENERATED_CARS_NUM 20

/* Maximum number of cars that will be generated (useful for debug) */
#define MAXIMUM_GENERATED_CARS_NUM 20

#define INVALID_INT_ID 255
#define INVALID_TL_ID  255

mtype = { RED, GREEN };

/* Current owner of intersection resource */
byte intersectionOwner[N_INTERSECTIONS];

/* Macro for obtaining intersection resource */
#define lockIntersection( intId, tlId )               \
end:                                                  \
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
#define unlockIntersection( intId ) \
  intersectionOwner[intId] = INVALID_TL_ID

/* Single traffic light dependent intersections.
 * Last element is INVALID_INT_ID.
 */
/* TODO: On this line:
 *   typedef singleDependentIntersections { byte intId[N_INTERSECTIONS + 1] };
 * compiler complains:
 *   Error: syntax error saw ''+' = 43'
 */
typedef singleDependentIntersections { byte intId[N_INTERSECTIONS_PLUS_ONE] };

/* All traffic lights dependent intersections */
singleDependentIntersections dependentIntersections[N_TRAFFIC_LIGHTS];

/* Queue of cars for each traffic light */
chan cars[N_TRAFFIC_LIGHTS] = [CARS_QUEUE_LEN] of { int };

/* Traffic light state */
mtype tlColor[N_TRAFFIC_LIGHTS];

/* Main traffic light process */
proctype TrafficLight( byte tlId )
{
  int carId;
  byte i;

  assert(tlId != INVALID_TL_ID);
  assert(tlColor[tlId] == RED);
  
  do
  :: cars[tlId] ? [carId] ->
    /* Cars in queue */
  
    /* Lock dependent intersections */
    i = 0;
    do
    :: dependentIntersections[tlId].intId[i] != INVALID_INT_ID ->
      lockIntersection(dependentIntersections[tlId].intId[i], tlId);
      i++;
    :: else ->
      break;
    od;
    
    /* Allow passing */
    atomic 
    {
      printf("MSC: Traffic light #%d: GREEN\n", tlId);
      tlColor[tlId] = GREEN;
    };
    
    /* Pass car */
    atomic
    {
      cars[tlId] ? carId;
      printf("MSC: Traffix light #%d: pass car #%d\n", tlId, carId);
    };
    
    /* Forbid passing */
    atomic
    {
      printf("MSC: Traffic light #%d: RED\n", tlId);
      tlColor[tlId] = RED;
    };
    
    /* Release dependent intersections */
    i = 0;
    do
    :: dependentIntersections[tlId].intId[i] != INVALID_INT_ID ->
      unlockIntersection(dependentIntersections[tlId].intId[i]);
      i++;
    :: else ->
      break;
    od;
  od
}

/* Cars generator process */
proctype CarsGenerator()
{
  byte tlId;
  int carId;

  carId = 0;
  do
  :: true ->
    if
    :: (carId >= MAXIMUM_GENERATED_CARS_NUM) ->
      break;
    :: else ->
      skip;
    fi;
  
    /* Generate car (probably) */
  
    tlId = 0;
    do
    :: (tlId < N_TRAFFIC_LIGHTS) ->
      if
      :: true ->
        /* Generate car and exit cycle */
        cars[tlId] ! carId;
        carId++;
        break
      :: true ->
        /* Skip car generation for current traffic light */
        skip
      fi;
      tlId++;
    :: else ->
      break;
    od;

  :: carId >= MINIMUM_GENERATED_CARS_NUM ->
    /* Minimum number of cars already genereted.
     * Nondeterministically stop car generation.
     */
    
    if
    :: true ->
      break;
    :: true ->
      skip
    fi

  :: else ->
    /* Don't generate car */
    skip
  od
}

/* The main model function */
init
{
  byte tlId, intId, intIdx;
  
  /* Configure traffic light intersections */
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
   * Looks like metropolitan map, yeah :)
   */
  /* NOTE: Intersections should be specified in incrementing order! */
  dependentIntersections[0].intId[0] = 0;
  dependentIntersections[0].intId[1] = 1;
  dependentIntersections[0].intId[2] = 2;
  dependentIntersections[0].intId[3] = INVALID_INT_ID;

  dependentIntersections[1].intId[0] = 0;
  dependentIntersections[1].intId[1] = 3;
  dependentIntersections[1].intId[2] = INVALID_INT_ID;

  dependentIntersections[2].intId[0] = 1;
  dependentIntersections[2].intId[1] = 4;
  dependentIntersections[2].intId[2] = INVALID_INT_ID;

  dependentIntersections[3].intId[0] = 2;
  dependentIntersections[3].intId[1] = 3;
  dependentIntersections[3].intId[2] = 4;
  dependentIntersections[3].intId[3] = INVALID_INT_ID;

  /* Check incrementing order of intersections */
  tlId = 0;
  do
  :: tlId < N_TRAFFIC_LIGHTS ->
    assert(dependentIntersections[tlId].intId[0] != INVALID_INT_ID);
    intIdx = 1;
    do
    :: dependentIntersections[tlId].intId[intIdx] != INVALID_INT_ID ->
      assert(dependentIntersections[tlId].intId[intIdx] > dependentIntersections[tlId].intId[intIdx - 1]);
      intIdx++;
    :: else ->
      break;
    od;
    tlId++;
  :: else ->
    break;
  od;
  
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