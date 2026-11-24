#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "simulator/svdpi.h"

namespace {

template <typename Prototype, typename Routine>
bool HasPrototype(Routine*) {
  return std::is_same<Prototype, Routine>::value;
}

TEST(SvdpiRoutinePrototypes, TheSelectUtilitiesHaveTheListingsPrototypes) {
  EXPECT_TRUE(
      (HasPrototype<svLogic(const svLogicVecVal*, int)>(&svGetBitselLogic)));
  EXPECT_TRUE((HasPrototype<void(svBitVecVal*, int, svBit)>(&svPutBitselBit)));
  EXPECT_TRUE(
      (HasPrototype<void(svLogicVecVal*, int, svLogic)>(&svPutBitselLogic)));
  EXPECT_TRUE((HasPrototype<void(svBitVecVal*, const svBitVecVal*, int, int)>(
      &svGetPartselBit)));
  EXPECT_TRUE(
      (HasPrototype<void(svLogicVecVal*, const svLogicVecVal*, int, int)>(
          &svGetPartselLogic)));
  EXPECT_TRUE((HasPrototype<void(svBitVecVal*, svBitVecVal, int, int)>(
      &svPutPartselBit)));
  EXPECT_TRUE((HasPrototype<void(svLogicVecVal*, svLogicVecVal, int, int)>(
      &svPutPartselLogic)));
}

TEST(SvdpiRoutinePrototypes,
     TheArrayQueriesAndPointersHaveTheListingsPrototypes) {
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle, int)>(&svLeft)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle, int)>(&svRight)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle, int)>(&svLow)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle, int)>(&svHigh)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle, int)>(&svIncrement)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle, int)>(&svSize)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle)>(&svDimensions)));
  EXPECT_TRUE((HasPrototype<int(svOpenArrayHandle)>(&svSizeOfArray)));
  EXPECT_TRUE((HasPrototype<void*(svOpenArrayHandle)>(&svGetArrayPtr)));
  EXPECT_TRUE(
      (HasPrototype<void*(svOpenArrayHandle, int, ...)>(&svGetArrElemPtr)));
  EXPECT_TRUE((HasPrototype<void*(svOpenArrayHandle, int)>(&svGetArrElemPtr1)));
  EXPECT_TRUE(
      (HasPrototype<void*(svOpenArrayHandle, int, int)>(&svGetArrElemPtr2)));
  EXPECT_TRUE((HasPrototype<void*(svOpenArrayHandle, int, int, int)>(
      &svGetArrElemPtr3)));
}

TEST(SvdpiRoutinePrototypes, TheVectorCopiesHaveTheListingsPrototypes) {
  EXPECT_TRUE(
      (HasPrototype<void(svOpenArrayHandle, const svBitVecVal*, int, ...)>(
          &svPutBitArrElemVecVal)));
  EXPECT_TRUE((HasPrototype<void(svBitVecVal*, svOpenArrayHandle, int, ...)>(
      &svGetBitArrElemVecVal)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, const svBitVecVal*, int)>(
      &svPutBitArrElem1VecVal)));
  EXPECT_TRUE((HasPrototype<void(svBitVecVal*, svOpenArrayHandle, int)>(
      &svGetBitArrElem1VecVal)));
  EXPECT_TRUE(
      (HasPrototype<void(svOpenArrayHandle, const svBitVecVal*, int, int)>(
          &svPutBitArrElem2VecVal)));
  EXPECT_TRUE((HasPrototype<void(svBitVecVal*, svOpenArrayHandle, int, int)>(
      &svGetBitArrElem2VecVal)));
  EXPECT_TRUE(
      (HasPrototype<void(svOpenArrayHandle, const svBitVecVal*, int, int, int)>(
          &svPutBitArrElem3VecVal)));
  EXPECT_TRUE(
      (HasPrototype<void(svBitVecVal*, svOpenArrayHandle, int, int, int)>(
          &svGetBitArrElem3VecVal)));
  EXPECT_TRUE(
      (HasPrototype<void(svOpenArrayHandle, const svLogicVecVal*, int, ...)>(
          &svPutLogicArrElemVecVal)));
  EXPECT_TRUE((HasPrototype<void(svLogicVecVal*, svOpenArrayHandle, int, ...)>(
      &svGetLogicArrElemVecVal)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, const svLogicVecVal*, int)>(
      &svPutLogicArrElem1VecVal)));
  EXPECT_TRUE((HasPrototype<void(svLogicVecVal*, svOpenArrayHandle, int)>(
      &svGetLogicArrElem1VecVal)));
  EXPECT_TRUE(
      (HasPrototype<void(svOpenArrayHandle, const svLogicVecVal*, int, int)>(
          &svPutLogicArrElem2VecVal)));
  EXPECT_TRUE((HasPrototype<void(svLogicVecVal*, svOpenArrayHandle, int, int)>(
      &svGetLogicArrElem2VecVal)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, const svLogicVecVal*, int,
                                 int, int)>(&svPutLogicArrElem3VecVal)));
  EXPECT_TRUE(
      (HasPrototype<void(svLogicVecVal*, svOpenArrayHandle, int, int, int)>(
          &svGetLogicArrElem3VecVal)));
}

TEST(SvdpiRoutinePrototypes,
     TheScalarElementRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE(
      (HasPrototype<svBit(svOpenArrayHandle, int, ...)>(&svGetBitArrElem)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svBit, int, ...)>(
      &svPutBitArrElem)));
  EXPECT_TRUE((HasPrototype<svBit(svOpenArrayHandle, int)>(&svGetBitArrElem1)));
  EXPECT_TRUE(
      (HasPrototype<void(svOpenArrayHandle, svBit, int)>(&svPutBitArrElem1)));
  EXPECT_TRUE(
      (HasPrototype<svBit(svOpenArrayHandle, int, int)>(&svGetBitArrElem2)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svBit, int, int)>(
      &svPutBitArrElem2)));
  EXPECT_TRUE((HasPrototype<svBit(svOpenArrayHandle, int, int, int)>(
      &svGetBitArrElem3)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svBit, int, int, int)>(
      &svPutBitArrElem3)));
  EXPECT_TRUE(
      (HasPrototype<svLogic(svOpenArrayHandle, int, ...)>(&svGetLogicArrElem)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svLogic, int, ...)>(
      &svPutLogicArrElem)));
  EXPECT_TRUE(
      (HasPrototype<svLogic(svOpenArrayHandle, int)>(&svGetLogicArrElem1)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svLogic, int)>(
      &svPutLogicArrElem1)));
  EXPECT_TRUE((
      HasPrototype<svLogic(svOpenArrayHandle, int, int)>(&svGetLogicArrElem2)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svLogic, int, int)>(
      &svPutLogicArrElem2)));
  EXPECT_TRUE((HasPrototype<svLogic(svOpenArrayHandle, int, int, int)>(
      &svGetLogicArrElem3)));
  EXPECT_TRUE((HasPrototype<void(svOpenArrayHandle, svLogic, int, int, int)>(
      &svPutLogicArrElem3)));
}

TEST(SvdpiRoutinePrototypes,
     TheContextAndTimeRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE((HasPrototype<const char*()>(&svDpiVersion)));
  EXPECT_TRUE((HasPrototype<svScope()>(&svGetScope)));
  EXPECT_TRUE((HasPrototype<svScope(svScope)>(&svSetScope)));
  EXPECT_TRUE((HasPrototype<const char*(svScope)>(&svGetNameFromScope)));
  EXPECT_TRUE((HasPrototype<svScope(const char*)>(&svGetScopeFromName)));
  EXPECT_TRUE((HasPrototype<int(svScope, void*, void*)>(&svPutUserData)));
  EXPECT_TRUE((HasPrototype<void*(svScope, void*)>(&svGetUserData)));
  EXPECT_TRUE((HasPrototype<int(const char**, int*)>(&svGetCallerInfo)));
  EXPECT_TRUE((HasPrototype<int()>(&svIsDisabledState)));
  EXPECT_TRUE((HasPrototype<void()>(&svAckDisabledState)));
  EXPECT_TRUE((HasPrototype<int(svScope, svTimeVal*)>(&svGetTime)));
  EXPECT_TRUE((HasPrototype<int(svScope, int32_t*)>(&svGetTimeUnit)));
  EXPECT_TRUE((HasPrototype<int(svScope, int32_t*)>(&svGetTimePrecision)));
}

}  // namespace
