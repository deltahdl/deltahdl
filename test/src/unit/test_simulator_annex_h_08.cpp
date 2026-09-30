#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_call.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.8 (Argument passing modes) defines the ways to pass arguments in
// the C layer of the DPI, and §H.8.1 gives the overview: an argument is
// generally passed by some form of reference, except a small value of an
// input argument, which is passed by value, and the function result, which
// being restricted to small values is passed by value, directly returned;
// a formal other than an open array is passed by direct reference or by
// value and so is directly accessible in C, and an open array formal is
// passed by handle and reached through library functions. The cases check
// which mode each formal takes and how the mode shows in the C type.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8: a small input is passed by value, a small output or inout and any
// packed array by reference, and an open array by handle whatever its type
// or direction.
TEST(DpiArgumentPassingModes, EachFormalIsPassedInOneOfThreeModes) {
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kInput), false),
            DpiPassingMode::kByValue);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kString, Direction::kInput), false),
            DpiPassingMode::kByValue);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kOutput), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kInout), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kBit, Direction::kInput, 8), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInteger, Direction::kInput), false),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kBit, Direction::kInput, 8), true),
            DpiPassingMode::kByHandle);
  EXPECT_EQ(DpiPassingModeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kOutput), true),
            DpiPassingMode::kByHandle);
}

// §H.8: the mode is what the C type shows -- a value's type as it is, a
// reference as a pointer to it, a handle as svOpenArrayHandle -- and a
// formal passed by value or by reference is directly accessible in C where
// one passed by handle is reached through the library functions.
TEST(DpiArgumentPassingModes, TheModeShowsInTheCType) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), false),
      "const int");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), false),
      "int*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), true),
      "const svOpenArrayHandle");
  EXPECT_TRUE(DpiFormalIsDirectlyAccessibleInC(DpiPassingMode::kByValue));
  EXPECT_TRUE(DpiFormalIsDirectlyAccessibleInC(DpiPassingMode::kByReference));
  EXPECT_FALSE(DpiFormalIsDirectlyAccessibleInC(DpiPassingMode::kByHandle));
}

// §H.8.1: the function result, restricted to small values, is passed by
// value, directly returned.
TEST(DpiArgumentPassingModes, TheResultIsPassedByValue) {
  EXPECT_EQ(DpiPassingModeOfResult(), DpiPassingMode::kByValue);
}

// §H.8: the C function an import is called in takes each small input by value
// as its own C type and every other formal by reference, and returns a small
// result by value. The generated call reads a by-value formal out of its
// object and hands a by-reference one the object's address, a pointer being
// passed alike whatever it points at.
TEST(DpiCTrampolineSource, TheCallTakesTheH8PrototypeOfTheImport) {
  const DpiRtFunction kImport =
      CImport("mix", DataTypeKind::kInt,
              {CFormal("a", DataTypeKind::kInt, Direction::kInput),
               CFormal("b", DataTypeKind::kInt, Direction::kOutput),
               CFormal("c", DataTypeKind::kBit, Direction::kInput, 8),
               CFormal("s", DataTypeKind::kString, Direction::kInput)});
  const std::string kSource = DpiCTrampolineSource({&kImport});
  EXPECT_EQ(kSource.rfind("typedef unsigned char svBit;\n"
                          "typedef unsigned char svLogic;\n",
                          0),
            0U);
  EXPECT_NE(kSource.find("void deltahdl_dpi_trampoline_0(void (*symbol)(void), "
                         "void** args, void* result) {\n"
                         "  (void)args;\n"
                         "  (void)result;\n"
                         "  *(int*)result = ((int (*)(const int, void*, void*, "
                         "const char*))symbol)(*(const int*)args[0], args[1], "
                         "args[2], *(const char**)args[3]);\n"
                         "}\n"),
            std::string::npos)
      << kSource;
}

// §H.8.1 and §35.9: a function with no result stores none, one with no
// formals takes (void), and an imported task returns the int the disable
// protocol reads.
TEST(DpiCTrampolineSource, NoResultNoFormalsAndATaskEachTakeTheirOwnForm) {
  const DpiRtFunction kFunction = CImport("ping", DataTypeKind::kVoid, {});
  DpiRtFunction task = CImport("wait_for", DataTypeKind::kVoid, {});
  task.is_task = true;
  const std::string kSource = DpiCTrampolineSource({&kFunction, &task});
  EXPECT_NE(kSource.find("  ((void (*)(void))symbol)();\n"), std::string::npos)
      << kSource;
  EXPECT_NE(kSource.find("void deltahdl_dpi_trampoline_1("), std::string::npos);
  EXPECT_NE(kSource.find("  *(int*)result = ((int (*)(void))symbol)();\n"),
            std::string::npos)
      << kSource;
}

// §H.7.3: a formal laid out in C as C lays out an unpacked array or struct,
// and one whose type is named by an enumeration or a typedef, are not small
// values or packed arrays; the call of an import having one is not built, and
// the reason names the formal. A result §H.8.9 does not list is refused too.
TEST(DpiCTrampolineSource, AFormalOrResultWithNoCLayoutHereIsNamed) {
  DpiArg open = CFormal("elems", DataTypeKind::kInt, Direction::kInput);
  open.has_unpacked_dimensions = true;
  EXPECT_EQ(DpiImportNotCallableInC(CImport("f", DataTypeKind::kInt, {open})),
            "deltahdl does not yet lay out in C the type of its formal "
            "'elems'");
  EXPECT_NE(DpiImportNotCallableInC(CImport(
                "g", DataTypeKind::kVoid,
                {CFormal("e", DataTypeKind::kEnum, Direction::kInput)})),
            "");
  EXPECT_EQ(DpiImportNotCallableInC(CImport("h", DataTypeKind::kStruct, {})),
            "its result type is not one §H.8.9 lets a C function return");
  EXPECT_EQ(DpiImportNotCallableInC(CImport(
                "k", DataTypeKind::kLongint,
                {CFormal("t", DataTypeKind::kTime, Direction::kInput)})),
            "");
}

}  // namespace
