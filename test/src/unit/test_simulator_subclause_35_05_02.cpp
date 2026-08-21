#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.5.2: a pure function call may be eliminated when its result is unused,
// or replaced by a previously memoized result when the same input values
// recur. The DPI runtime carries an is_pure flag on each registered import
// so call-elision and memoization passes can identify candidates without
// re-inspecting the elaborated AST.

TEST(PureDpiImportRegistry, PureFlagSurvivesRegistration) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_p";
  func.sv_name = "sv_p";
  func.return_type = DataTypeKind::kInt;
  func.is_pure = true;
  rt.RegisterImport(std::move(func));

  const auto* found = rt.FindImport("sv_p");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_pure);
}

TEST(PureDpiImportRegistry, NonPureImportDistinguishable) {
  // A regular import (no pure property) round-trips with is_pure cleared so
  // optimization passes do not mis-classify it as elidable.
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_n";
  func.sv_name = "sv_n";
  func.return_type = DataTypeKind::kInt;
  rt.RegisterImport(std::move(func));

  const auto* found = rt.FindImport("sv_n");
  ASSERT_NE(found, nullptr);
  EXPECT_FALSE(found->is_pure);
}

// ---------------------------------------------------------------------------
// A pure function's call can be removed.
// ---------------------------------------------------------------------------
//
// §35.5.2 says what may be done with a call to a pure function rather than what
// the call does:
//
//   A pure function call can be eliminated if its result is not needed or if
//   the previous result for the same values of input arguments is available
//   somehow and can be reused without needing to recalculate. [...] Calls to
//   such functions can be removed by SystemVerilog compiler optimizations or
//   replaced with the values previously computed for the same values of the
//   input arguments.
//
// Both halves rest on the same two facts about the function, which the same
// paragraph states: it has no side effects whatsoever, and its result depends
// solely on the values of its input arguments. §35.5.1 says no SystemVerilog
// compiler can verify either, and the three bullets §35.5.2 goes on to list --
// no file operation, no reading or writing anything in the broadest sense, no
// access to persistent data such as a global or static variable -- are what the
// tool is entitled to assume of foreign code rather than anything it can check.
// So what a run can be held to is the licence: the call of a pure function is
// removable and no other import's is, and a pure call presenting values an
// earlier call already presented is answered from what that call computed
// instead of entering the foreign function again.
//
// DpiRuntime::ImportCallIsRemovable and DpiRuntime::CallImportReusingPureResult
// in src/simulator/dpi_runtime.h answer those two, and the cases below read
// them. The restrictions that decide which functions may carry the property at
// all -- nonvoid return, no output or inout formal, never a task -- are settled
// where a declaration is elaborated and are covered in
// test_elaborator_subclause_35_05_02.cpp.

// One import declared pure or not, and the count its foreign body keeps of how
// many times it was entered.
//
// The count is the one thing a case here needs that the return value cannot
// give it: a reused result and a recomputed one are the same value, so only the
// body can say whether it ran. Keeping such a count is a side effect §35.5.2
// forbids a pure function, which is what makes it a fair question to ask -- the
// body reports what the standard assumes never happens, so a case can tell a
// removed call from a made one.
struct CountingPureEntries {
  DpiRuntime rt;
  int entries = 0;

  explicit CountingPureEntries(bool is_pure) {
    DpiRtFunction func;
    func.c_name = "c_square";
    func.sv_name = "square";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
    func.is_pure = is_pure;
    func.impl = [this](const std::vector<DpiArgValue>& a) {
      ++entries;
      return DpiArgValue::FromInt(a[0].AsInt() * a[0].AsInt());
    };
    rt.RegisterImport(std::move(func));
  }

  // Calls the import on `x` through the entry point §35.5.2 licenses to reuse.
  int Squaring(int x) {
    return rt.CallImportReusingPureResult("square", {DpiArgValue::FromInt(x)})
        .AsInt();
  }
};

// §35.5.2 lets a compiler optimization remove the call of a pure function, and
// the property on the declaration is what says which calls those are.
TEST(PureDpiCallRemoval, APureImportsCallIsRemovable) {
  CountingPureEntries declared(/*is_pure=*/true);
  EXPECT_TRUE(declared.rt.ImportCallIsRemovable("square"));
}

// An import without the property is not removable. §35.5.1.3 leaves such a one
// free to write a file or manipulate a global variable, so removing its call
// would lose whatever it was written for.
TEST(PureDpiCallRemoval, AnImportWithoutThePropertyIsNotRemovable) {
  CountingPureEntries declared(/*is_pure=*/false);
  EXPECT_FALSE(declared.rt.ImportCallIsRemovable("square"));
}

// A name no declaration was registered under carries no property, so nothing
// licenses removing its call either.
TEST(PureDpiCallRemoval, AnUndeclaredNamesCallIsNotRemovable) {
  CountingPureEntries declared(/*is_pure=*/true);
  EXPECT_FALSE(declared.rt.ImportCallIsRemovable("cube"));
}

// The reuse itself: a second pure call presenting the value the first presented
// is replaced by what the first computed, so the foreign function is entered
// once for the two calls.
TEST(PureDpiCallRemoval, TheSecondPureCallOnOneValueIsNotComputed) {
  CountingPureEntries declared(/*is_pure=*/true);
  declared.Squaring(7);
  declared.Squaring(7);
  EXPECT_EQ(declared.entries, 1);
}

// And the value the second call yields is the one the first computed, which is
// what makes removing it sound rather than merely cheap. Without this the case
// above would hold of a runtime that skipped the second call and answered zero.
TEST(PureDpiCallRemoval, TheReusedValueIsWhatTheFirstCallComputed) {
  CountingPureEntries declared(/*is_pure=*/true);
  EXPECT_EQ(declared.Squaring(7), declared.Squaring(7));
}

// §35.5.2 offers the previous result for the same values of the input
// arguments, so a different value is computed afresh. A runtime keeping one
// result per import would answer 49 for the square of 8.
TEST(PureDpiCallRemoval, ADifferentValueIsComputedAfresh) {
  CountingPureEntries declared(/*is_pure=*/true);
  declared.Squaring(7);
  EXPECT_EQ(declared.Squaring(8), 64);
}

// The value is the whole of the question a reuse asks, so a second value
// entering the function leaves the first still answerable without entering it
// again.
TEST(PureDpiCallRemoval, AValueSeenBeforeIsStillReusedAfterAnother) {
  CountingPureEntries declared(/*is_pure=*/true);
  declared.Squaring(7);
  declared.Squaring(8);
  declared.Squaring(7);
  EXPECT_EQ(declared.entries, 2);
}

// An import without the property is entered on every call through the same
// entry point. This is what confines the reuse to §35.5.2's subject rather than
// applying it to whatever the caller happened to route this way.
TEST(PureDpiCallRemoval, AnImportWithoutThePropertyIsEnteredEveryTime) {
  CountingPureEntries declared(/*is_pure=*/false);
  declared.Squaring(7);
  declared.Squaring(7);
  EXPECT_EQ(declared.entries, 2);
}

// A call made the ordinary way is made, whatever this entry point has already
// answered for the same values. The optimization is something a caller asks
// for, so a caller that did not ask still gets its call.
TEST(PureDpiCallRemoval, AnOrdinaryCallIsMadeAfterAReusableOneWasAnswered) {
  CountingPureEntries declared(/*is_pure=*/true);
  declared.Squaring(7);
  declared.rt.CallImport("square", {DpiArgValue::FromInt(7)});
  EXPECT_EQ(declared.entries, 2);
}

}  // namespace
