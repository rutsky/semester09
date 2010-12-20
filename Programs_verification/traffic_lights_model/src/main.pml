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
#define N_INTERSECTIONS   5
/* Number of traffic lights */
#define N_TRAFFIC_LIGHTS  4
/* Maximum number of cars in signle traffig light queue */
#define CARS_QUEUE_LEN   10

#define INVALID_INT_ID 255
#define INVALID_TL_ID  255

mtype = { red, green };

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
#define unlockIntersection( intId ) \
  intersectionOwner[intId] = INVALID_TL_ID

/* Single traffic light dependent intersections.
 * Last element is INVALID_INT_ID.
 */
typedef singleDependentIntersections { byte intId[N_INTERSECTIONS + 1] };

/* All traffic lights dependent intersections */
singleDependentIntersections dependentIntersections[N_TRAFFIC_LIGHTS];

/* Queue of cars for each traffic light */
chan cars[N_TRAFFIC_LIGHTS] = [CARS_QUEUE_LEN] of { byte };

/* Traffic light state */
mtype tlColor[N_TRAFFIC_LIGHTS];

/* Main traffic light process */
proctype TrafficLight( byte tlId )
{
  byte car;
  byte i;

  assert(tlId != INVALID_TL_ID);
  assert(tlColor[tlId] == red);
  
  do
  :: cars[tlId] ? [car] ->
    /* Cars in queue */
  
    /* Lock dependent intersections */
    i = 0;
    do
    :: i < N_TRAFFIC_LIGHTS -> 
      lockIntersection(dependentIntersections[tlId].intId[i], tlId);
      i++;
    :: else ->
      break;
    }
    
    /* Allow passing */
    tlColor[tlId] = green;
    
    /* Pass car */
    cars[tlId] ? car;
    
    /* Forbid passing */
    tlColor[tlId] = red;
    
    /* Release dependent intersections */
    i = 0;
    do
    :: i < N_TRAFFIC_LIGHTS -> 
      unlockIntersection(dependentIntersections[tlId].intId[i]);
      i++;
    :: else ->
      break;
    }
    
  :: else -> 
    skip;
  od
}

/* Cars generator process */
proctype CarsGenerator()
{
  byte tlId;

  do
  :: true ->
    /* Generate car (probably) */
  
    // TODO: Compiler complains:
    // Error: syntax error saw 'an identifier' near 'N_TRAFFIC_LIGHTS'
    //for (tlId : 0..N_TRAFFIC_LIGHTS)
    for (tlId : 0..10)
    {
      if
      :: tlId >= N_TRAFFIC_LIGHTS ->
        break;
      :: else ->
        skip
      fi;
      
      if
      :: true ->
        /* Generate car and exit cycle */
        cars[tlId] ? 1;
        break
      :: true ->
        /* Skip car generation for current traffic light */
        skip
      fi
    }
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
    tlColor[tlId] = red;
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
