#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8.2 (Calling SystemVerilog tasks and functions from C): there is
// no difference in argument passing between a call from SystemVerilog to C
// and one from C to SystemVerilog; a task or function exported from
// SystemVerilog cannot have an open array as an argument, and apart from
// that the same types of formal can be declared for an export as for an
// import; a subroutine exported from SystemVerilog shall have the same
// function header in C as an imported function with the same result type
// and the same formal list would; for an argument passed by reference the
// actual to a SystemVerilog subroutine called from C shall be allocated
// with the layout SystemVerilog uses for the type, the caller being
// responsible for the allocation; and calling a SystemVerilog task from C
// is the same as calling a function except that the return type of an
// exported task is an int with the meaning §35.9 gives it. The cases check
// the header an export and an import share, the int an exported task
// returns, the open array an export may not take, and who allocates.

namespace {

DpiArg Formal(const char* name, DataTypeKind type, Direction direction,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.2: an export has the header in C that an import with the same
// result type and formal list has -- int f(const int a, svBitVecVal* b,
// const svLogicVecVal* c) for both -- and a void result is void.
TEST(DpiCallsFromC, AnExportHasTheHeaderAnImportWithTheSameListHas) {
  const std::vector<DpiArg> kFormals = {
      Formal("a", DataTypeKind::kInt, Direction::kInput),
      Formal("b", DataTypeKind::kBit, Direction::kOutput, 8),
      Formal("c", DataTypeKind::kLogic, Direction::kInput, 40)};
  EXPECT_EQ(DpiCFunctionHeader("f", DataTypeKind::kInt, kFormals),
            "int f(const int a, svBitVecVal* b, const svLogicVecVal* c)");
  EXPECT_EQ(
      DpiCHeaderOfExportedSubroutine("f", DataTypeKind::kInt, kFormals, false),
      DpiCFunctionHeader("f", DataTypeKind::kInt, kFormals));
  EXPECT_EQ(DpiCHeaderOfExportedSubroutine("g", DataTypeKind::kVoid, {}, false),
            "void g()");
  EXPECT_EQ(DpiCFunctionHeader("g", DataTypeKind::kVoid, {}), "void g()");
}

// §H.8.2: calling an exported task is calling a function whose return
// type is int, whatever result a task has none of.
TEST(DpiCallsFromC, AnExportedTaskReturnsAnInt) {
  const std::vector<DpiArg> kFormals = {
      Formal("a", DataTypeKind::kInt, Direction::kInput)};
  EXPECT_EQ(
      DpiCHeaderOfExportedSubroutine("t", DataTypeKind::kVoid, kFormals, true),
      "int t(const int a)");
  EXPECT_EQ(DpiCTypeOfExportedTaskResult(), "int");
}

// §H.8.2: an export cannot have an open array formal; apart from that the
// types an import's formals take are the types an export's may.
TEST(DpiCallsFromC, AnExportCannotHaveAnOpenArrayFormal) {
  EXPECT_FALSE(DpiExportFormalMayBeAnOpenArray());
  EXPECT_TRUE(DpiExportFormalMayHaveType(DataTypeKind::kInt));
  EXPECT_TRUE(DpiExportFormalMayHaveType(DataTypeKind::kBit));
  EXPECT_TRUE(DpiExportFormalMayHaveType(DataTypeKind::kString));
  EXPECT_FALSE(DpiExportFormalMayHaveType(DataTypeKind::kEvent));
}

// §H.8.2: an actual passed by reference to a SystemVerilog subroutine
// called from C is the caller's to allocate, in SystemVerilog's layout for
// the type, which for a packed array is the canonical one.
TEST(DpiCallsFromC, TheCallerAllocatesAnActualPassedByReference) {
  EXPECT_EQ(DpiSideAllocatingActualOfExportCall(), DpiMemorySide::kC);
  EXPECT_EQ(DpiRepresentationOfFormal(
                Formal("b", DataTypeKind::kBit, Direction::kOutput, 8)),
            DpiRepresentation::kCanonical);
}

}  // namespace
