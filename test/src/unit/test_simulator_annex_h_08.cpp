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

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

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

TEST(DpiArgumentPassingModes, TheResultIsPassedByValue) {
  EXPECT_EQ(DpiPassingModeOfResult(), DpiPassingMode::kByValue);
}

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
