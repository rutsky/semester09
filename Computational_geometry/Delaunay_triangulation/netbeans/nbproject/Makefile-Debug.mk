#
# Generated Makefile - do not edit!
#
# Edit the Makefile in the project folder instead (../Makefile). Each target
# has a -pre and a -post target defined where you can add customized code.
#
# This makefile implements configuration specific macros and targets.


# Environment
MKDIR=mkdir
CP=cp
CCADMIN=CCadmin
RANLIB=ranlib
CC=gcc
CCC=g++
CXX=g++
FC=gfortran
AS=as

# Macros
CND_PLATFORM=GNU-Linux-x86
CND_CONF=Debug
CND_DISTDIR=dist

# Include project Makefile
include Makefile

# Object Directory
OBJECTDIR=build/${CND_CONF}/${CND_PLATFORM}

# Object Files
OBJECTFILES= \
	${OBJECTDIR}/_ext/_DOTDOT/delaunay/main.o

# C Compiler Flags
CFLAGS=

# CC Compiler Flags
CCFLAGS=-I../boost -I../include -I/usr/include -frounding-math -DHAVE_CGAL -DUSE_CGAL_ON_INEXACT
CXXFLAGS=-I../boost -I../include -I/usr/include -frounding-math -DHAVE_CGAL -DUSE_CGAL_ON_INEXACT

# Fortran Compiler Flags
FFLAGS=

# Assembler Flags
ASFLAGS=

# Link Libraries and Options
LDLIBSOPTIONS=

# Build Targets
.build-conf: ${BUILD_SUBPROJECTS}
	${MAKE}  -f nbproject/Makefile-Debug.mk dist/Debug/GNU-Linux-x86/netbeans

dist/Debug/GNU-Linux-x86/netbeans: ${OBJECTFILES}
	${MKDIR} -p dist/Debug/GNU-Linux-x86
	${LINK.cc} -L/usr/lib -lCGAL -lCGAL_Core -o ${CND_DISTDIR}/${CND_CONF}/${CND_PLATFORM}/netbeans ${OBJECTFILES} ${LDLIBSOPTIONS} 

${OBJECTDIR}/_ext/_DOTDOT/delaunay/main.o: nbproject/Makefile-${CND_CONF}.mk ../delaunay/main.cpp 
	${MKDIR} -p ${OBJECTDIR}/_ext/_DOTDOT/delaunay
	${RM} $@.d
	$(COMPILE.cc) -g -Wall -MMD -MP -MF $@.d -o ${OBJECTDIR}/_ext/_DOTDOT/delaunay/main.o ../delaunay/main.cpp

# Subprojects
.build-subprojects:

# Clean Targets
.clean-conf: ${CLEAN_SUBPROJECTS}
	${RM} -r build/Debug
	${RM} dist/Debug/GNU-Linux-x86/netbeans

# Subprojects
.clean-subprojects:

# Enable dependency checking
.dep.inc: .depcheck-impl

include .dep.inc
