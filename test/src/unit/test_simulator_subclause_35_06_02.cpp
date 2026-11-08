#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_bump_import.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(actuals[0].AsInt(), 99);
}

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

TEST(DpiOutputInoutValueChanges, UnchangedActualRaisesNoEvent) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_passthru";
  func.sv_name = "passthru";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"io", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
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

TEST(DpiOutputInoutValueChanges, InputArgNeverRaisesEvent) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_clobber_in";
  func.sv_name = "clobber_in";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"i", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(-1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("clobber_in", actuals, changes);

  EXPECT_TRUE(changes.empty());
  EXPECT_EQ(actuals[0].AsInt(), 5);
}

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
    a[0] = DpiArgValue::FromInt(123);
    a[1] = DpiArgValue::FromInt(55);
    a[2] = DpiArgValue::FromInt(a[2].AsInt());
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(3),
                                      DpiArgValue::FromInt(8),
                                      DpiArgValue::FromInt(70)};
  std::vector<DpiArgValueChange> changes;
  rt.CallImportDetectingChanges("mixed", actuals, changes);

  ASSERT_EQ(changes.size(), 1u);
  EXPECT_EQ(changes[0].index, 1u);
  EXPECT_EQ(changes[0].old_value.AsInt(), 8);
  EXPECT_EQ(changes[0].new_value.AsInt(), 55);
  EXPECT_EQ(actuals[0].AsInt(), 3);
  EXPECT_EQ(actuals[2].AsInt(), 70);
}

TEST(DpiOutputInoutValueChanges, OutputWrittenSameValueRaisesNoEvent) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_out_same";
  func.sv_name = "out_same";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
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

TEST(DpiOutputInoutValueChanges, ChangedArgReportedAtItsDeclaredIndex) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_second_only";
  func.sv_name = "second_only";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"a", DataTypeKind::kInt, Direction::kInout},
               DpiArg{"b", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(a[0].AsInt());
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
  EXPECT_EQ(actuals[0].AsInt(), 10);
}

struct AnOutputActual {
  uint32_t width = 32;
  bool is_4state = true;
  std::string_view arg = "a";
};

struct AnOutputActualInADesign {
  DpiRuntime rt;
  SimFixture f;
  int events = 0;

  AnOutputActualInADesign(AnOutputActual decl, int32_t actual, int32_t wrote) {
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
    auto* var = f.ctx.CreateVariable("a", decl.width);
    var->is_4state = decl.is_4state;
    var->value =
        MakeLogic4VecVal(f.arena, decl.width, static_cast<uint64_t>(actual));
    int* events_slot = &events;
    var->AddWatcher([events_slot]() {
      ++*events_slot;
      return false;
    });
    EvalFunctionCall(ParseExprFrom("set_out(" + std::string(decl.arg) + ")", f),
                     f.ctx, f.arena);
  }

  uint64_t Actual() { return f.ctx.FindVariable("a")->value.ToUint64(); }
};

TEST(DpiValueChangeInADesign, AnOutputActualAlteredByAnImportRaisesOneEvent) {
  AnOutputActualInADesign run(AnOutputActual{}, 7, 99);
  EXPECT_EQ(run.events, 1);
}

TEST(DpiValueChangeInADesign, ThePropagatedValueIsWhatTheImportWrote) {
  AnOutputActualInADesign run(AnOutputActual{}, 7, 99);
  EXPECT_EQ(run.Actual(), 99U);
}

TEST(DpiValueChangeInADesign, AnUnalteredOutputActualRaisesNoEvent) {
  AnOutputActualInADesign run(AnOutputActual{}, 50, 50);
  EXPECT_EQ(run.events, 0);
}

TEST(DpiValueChangeInADesign, ATruncatedWritebackOfTheSameValueRaisesNoEvent) {
  AnOutputActualInADesign run(AnOutputActual{4, false, "a"}, 5, 21);

  EXPECT_EQ(run.events, 0);
  EXPECT_EQ(run.Actual(), 5U);
}

TEST(DpiValueChangeInADesign, ATruncatedWritebackToANewValueStillRaisesOne) {
  AnOutputActualInADesign run(AnOutputActual{4, false, "a"}, 5, 22);

  EXPECT_EQ(run.events, 1);
  EXPECT_EQ(run.Actual(), 6U);
}

TEST(DpiValueChangeInADesign, AnOutputActualNamingABitSelectStillPropagates) {
  AnOutputActualInADesign run(AnOutputActual{4, false, "a[1]"}, 5, 99);

  EXPECT_EQ(run.events, 1);
  EXPECT_EQ(run.Actual(), 7U);
}

}  // namespace
