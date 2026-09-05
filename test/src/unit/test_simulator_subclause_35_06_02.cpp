#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_bump_import.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §35.6.2 — Value changes for output and inout arguments. The SystemVerilog
// simulator is responsible for handling the value changes of an imported
// function's output and inout arguments; such changes shall be detected and
// handled after control returns from the imported function to SystemVerilog.
// The propagation happens as if the actual were assigned the formal immediately
// after the return, and with more than one argument the assignments and their
// value-change events follow general SystemVerilog ordering. These tests drive
// DpiRuntime::CallImportDetectingChanges and observe the ordered value-change
// events it raises once control has returned from the import.

// An output argument the call writes to a new value is detected and handled
// after control returns: exactly one value-change event is raised for it,
// bracketing the actual's value before and after the call.
TEST(DpiOutputInoutValueChanges, OutputChangeRaisesEventAfterReturn) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_set_out";
  func.sv_name = "set_out";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(99);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("set_out", actuals, changes);

  ASSERT_EQ(changes.size(), 1u);
  EXPECT_EQ(changes[0].index, 0u);
  EXPECT_EQ(changes[0].old_value.AsInt(), 7);
  EXPECT_EQ(changes[0].new_value.AsInt(), 99);
  // The actual itself carries the propagated new value.
  EXPECT_EQ(actuals[0].AsInt(), 99);
}

// An inout argument whose value the call changes likewise raises a single
// value-change event after the return.
TEST(DpiOutputInoutValueChanges, InoutChangeRaisesEvent) {
  DpiRuntime rt;
  RegisterBumpImport(rt);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(41)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("bump", actuals, changes);

  ASSERT_EQ(changes.size(), 1u);
  EXPECT_EQ(changes[0].index, 0u);
  EXPECT_EQ(changes[0].old_value.AsInt(), 41);
  EXPECT_EQ(changes[0].new_value.AsInt(), 42);
}

// Value-change semantics: an actual the call leaves at its prior value raises
// no event. Here the foreign code writes the inout's existing value straight
// back, so there is no change to propagate.
TEST(DpiOutputInoutValueChanges, UnchangedActualRaisesNoEvent) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_passthru";
  func.sv_name = "passthru";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"io", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    // Write the same value the inout already held.
    a[0] = DpiArgValue::FromInt(a[0].AsInt());
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(13)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("passthru", actuals, changes);

  EXPECT_TRUE(changes.empty());
  EXPECT_EQ(actuals[0].AsInt(), 13);
}

// §35.6.2 governs only output and inout arguments. An input argument is passed
// by value, so anything the foreign code does to its copy never reaches the
// actual and never produces a value-change event.
TEST(DpiOutputInoutValueChanges, InputArgNeverRaisesEvent) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_clobber_in";
  func.sv_name = "clobber_in";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"i", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(-1);  // discarded: input is copy-in only
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("clobber_in", actuals, changes);

  EXPECT_TRUE(changes.empty());
  EXPECT_EQ(actuals[0].AsInt(), 5);
}

// With more than one argument, the value-change events are reported in
// declaration order, following the ordering general SystemVerilog rules impose
// on the assignments and their propagation.
TEST(DpiOutputInoutValueChanges, MultipleEventsInDeclarationOrder) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_set_two";
  func.sv_name = "set_two";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"a", DataTypeKind::kInt, Direction::kOutput},
               DpiArg{"b", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(100);
    a[1] = DpiArgValue::FromInt(200);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(1),
                                      DpiArgValue::FromInt(2)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("set_two", actuals, changes);

  ASSERT_EQ(changes.size(), 2u);
  EXPECT_EQ(changes[0].index, 0u);
  EXPECT_EQ(changes[0].new_value.AsInt(), 100);
  EXPECT_EQ(changes[1].index, 1u);
  EXPECT_EQ(changes[1].new_value.AsInt(), 200);
}

// Edge: a call mixing all three directions where only some output/inout actuals
// change. Only the genuinely changed output/inout actuals are reported, each at
// its own argument index, and the input is ignored entirely.
TEST(DpiOutputInoutValueChanges, MixedDirectionsReportOnlyChangedOutInout) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_mixed";
  func.sv_name = "mixed";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"i", DataTypeKind::kInt, Direction::kInput},
               DpiArg{"o", DataTypeKind::kInt, Direction::kOutput},
               DpiArg{"io", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(123);  // input write: discarded, no event
    a[1] = DpiArgValue::FromInt(55);   // output: changes from 8 -> 55
    a[2] = DpiArgValue::FromInt(a[2].AsInt());  // inout: written back unchanged
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(3),
                                      DpiArgValue::FromInt(8),
                                      DpiArgValue::FromInt(70)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("mixed", actuals, changes);

  // Only the output at index 1 changed; the input and the unchanged inout
  // raise nothing.
  ASSERT_EQ(changes.size(), 1u);
  EXPECT_EQ(changes[0].index, 1u);
  EXPECT_EQ(changes[0].old_value.AsInt(), 8);
  EXPECT_EQ(changes[0].new_value.AsInt(), 55);
  EXPECT_EQ(actuals[0].AsInt(), 3);   // input actual untouched
  EXPECT_EQ(actuals[2].AsInt(), 70);  // inout actual unchanged
}

// Value-change semantics for the output direction: an output actual the call
// writes back at its prior value raises no event, just as for inout. This
// covers the output branch of the no-change case.
TEST(DpiOutputInoutValueChanges, OutputWrittenSameValueRaisesNoEvent) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_out_same";
  func.sv_name = "out_same";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    // Write back the value the actual already held before the call.
    a[0] = DpiArgValue::FromInt(50);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(50)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("out_same", actuals, changes);

  EXPECT_TRUE(changes.empty());
  EXPECT_EQ(actuals[0].AsInt(), 50);
}

// Value changes are detected and propagated for non-integer types too: the
// detection compares same-typed values and the event carries the propagated
// value. Here a longint inout the call alters raises one event bracketing the
// 64-bit values, exercising the non-int change-detection path.
TEST(DpiOutputInoutValueChanges, LongintChangeDetectedAndPropagated) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_wide";
  func.sv_name = "wide";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"io", DataTypeKind::kLongint, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromLongint(a[0].AsLongint() + 1000);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {
      DpiArgValue::FromLongint(9'000'000'000LL)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("wide", actuals, changes);

  ASSERT_EQ(changes.size(), 1u);
  EXPECT_EQ(changes[0].index, 0u);
  EXPECT_EQ(changes[0].old_value.AsLongint(), 9'000'000'000LL);
  EXPECT_EQ(changes[0].new_value.AsLongint(), 9'000'001'000LL);
  EXPECT_EQ(actuals[0].AsLongint(), 9'000'001'000LL);
}

// Multi-argument ordering with a non-contiguous changed subset: of two inout
// arguments only the second changes, so a single event is reported at index 1.
// The event's index reflects the argument's declared position, not its rank
// among the changed arguments.
TEST(DpiOutputInoutValueChanges, ChangedArgReportedAtItsDeclaredIndex) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_second_only";
  func.sv_name = "second_only";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"a", DataTypeKind::kInt, Direction::kInout},
               DpiArg{"b", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(a[0].AsInt());  // unchanged
    a[1] = DpiArgValue::FromInt(a[1].AsInt() + 5);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(10),
                                      DpiArgValue::FromInt(20)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("second_only", actuals, changes);

  ASSERT_EQ(changes.size(), 1u);
  EXPECT_EQ(changes[0].index, 1u);
  EXPECT_EQ(changes[0].old_value.AsInt(), 20);
  EXPECT_EQ(changes[0].new_value.AsInt(), 25);
  EXPECT_EQ(actuals[0].AsInt(), 10);  // first inout unchanged, no event
}

// ---------------------------------------------------------------------------
// The same rule, asked of a call a design makes.
//
// The cases above read the events out of the vector DpiRuntime fills. A design
// has no such vector: what §35.6.2 calls handling the change is the assignment
// to the actual, and what a design observes is the propagation that assignment
// starts. EvalDpiCall in src/simulator/eval_function_dpi.cpp is where the two
// meet, and Variable::NotifyWatchers is what a value change reaches.
// ---------------------------------------------------------------------------

// A design holding one variable `a` set to `actual`, handed to an import whose
// foreign body leaves `wrote` in its output formal. `events` counts the times
// the variable's value change was propagated, and Actual() is what it holds
// once the call has returned.
struct AnOutputActualInADesign {
  DpiRuntime rt;
  SimFixture f;
  int events = 0;

  AnOutputActualInADesign(int32_t actual, int32_t wrote) {
    DpiRtFunction func;
    func.c_name = "c_set_out";
    func.sv_name = "set_out";
    func.return_type = DataTypeKind::kVoid;
    func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
    func.arg_impl = [wrote](std::vector<DpiArgValue>& a) {
      a[0] = DpiArgValue::FromInt(wrote);
      return DpiArgValue::FromInt(0);
    };
    rt.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&rt);
    auto* var = f.ctx.CreateVariable("a", 32);
    var->value = MakeLogic4VecVal(f.arena, 32, static_cast<uint64_t>(actual));
    int* events_slot = &events;
    // Returning false keeps the watcher registered, so a second propagation
    // would be counted too rather than going unseen.
    var->AddWatcher([events_slot]() {
      ++*events_slot;
      return false;
    });
    EvalFunctionCall(ParseExprFrom("set_out(a)", f), f.ctx, f.arena);
  }

  uint64_t Actual() { return f.ctx.FindVariable("a")->value.ToUint64(); }
};

// §35.6.2: the value change of an output actual is detected and handled after
// control returns from the imported function, and handling it is one
// propagation of one assignment. The foreign body writes 99 over a 7, so the
// design sees the change once.
TEST(DpiValueChangeInADesign, AnOutputActualAlteredByAnImportRaisesOneEvent) {
  AnOutputActualInADesign run(/*actual=*/7, /*wrote=*/99);
  EXPECT_EQ(run.events, 1);
}

// The change that was propagated is the one the import made, which is what
// makes the count above a value change rather than a bare notification.
TEST(DpiValueChangeInADesign, ThePropagatedValueIsWhatTheImportWrote) {
  AnOutputActualInADesign run(/*actual=*/7, /*wrote=*/99);
  EXPECT_EQ(run.Actual(), 99U);
}

// §35.6.2 has the propagation happen "as if the actual argument was assigned
// the formal output value immediately after the return", and an assignment of
// the value a variable already holds is not a value change. The foreign body
// writes back the 50 the actual came in with, so the design sees nothing.
TEST(DpiValueChangeInADesign, AnUnalteredOutputActualRaisesNoEvent) {
  AnOutputActualInADesign run(/*actual=*/50, /*wrote=*/50);
  EXPECT_EQ(run.events, 0);
}

}  // namespace
