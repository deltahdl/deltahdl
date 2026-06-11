#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// §35.2.2 is an overview subclause: it states the data-type model that governs
// DPI without adding its own BNF or any "shall". Its concrete rules are
// delegated -- result types restricted to small values (§35.5.5) and open-array
// formals (§35.5.6.1), both already in place -- so the clause is satisfied by
// observing that the existing parser realizes its overview claims. The
// production code under observation is ParseDpiImport / ParseDpiExport, which
// reach the type system only through ParseDataType (SystemVerilog type syntax)
// and expose no path for a foreign-language type.

// §35.2.2: SystemVerilog data types are the sole data types that cross the
// boundary. On the import direction this is observable directly: the result and
// every formal argument of an accepted import declaration carry SystemVerilog
// data-type kinds, parsed with the SystemVerilog type syntax.
TEST_F(DpiParseTest, SystemVerilogTypesCrossOnImport) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int compute(\n"
      "    input logic [31:0] data,\n"
      "    input int count\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  // The result type that crosses back is a SystemVerilog type.
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kInt);
  ASSERT_EQ(items[0]->func_args.size(), 2u);
  // The argument types that cross are SystemVerilog types.
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(diag_.HasErrors());
}

// §35.2.2: the boundary is crossed by SystemVerilog data types in EITHER
// direction. On the export direction the declaration names a SystemVerilog
// subroutine rather than restating a signature, so the data that crosses is
// exchanged through that subroutine's own SystemVerilog-typed interface. The
// export declaration parses cleanly and is recorded as a DPI export.
TEST_F(DpiParseTest, SystemVerilogTypesCrossOnExport) {
  auto* unit = Parse(
      "module m;\n"
      "  function int sv_func(input int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[1]->name, "sv_func");
  EXPECT_FALSE(diag_.HasErrors());
}

// §35.2.2: it is not possible to import data types or to use the type syntax of
// another language; the type that crosses can only be named with SystemVerilog
// syntax. A user-defined SystemVerilog type (a typedef) is accordingly accepted
// as a DPI formal and recorded as a named SystemVerilog type -- there is no
// alternative, foreign-language spelling that the parser would accept here.
TEST_F(DpiParseTest, OnlySystemVerilogTypeSyntaxNamesACrossingType) {
  auto* unit = Parse(
      "module m;\n"
      "  typedef int my_int_t;\n"
      "  import \"DPI-C\" function void take(input my_int_t value);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[1]->func_args.size(), 1u);
  EXPECT_EQ(items[1]->func_args[0].data_type.kind, DataTypeKind::kNamed);
  EXPECT_FALSE(diag_.HasErrors());
}

// §35.2.2 edge: even data that originates in the foreign language crosses the
// boundary as a SystemVerilog type, not as an imported foreign type. The
// opaque-handle type used to convey a foreign-language pointer is the
// SystemVerilog `chandle` type; an import declaring it parses with that
// SystemVerilog data-type kind, with no foreign type syntax involved.
TEST_F(DpiParseTest, ForeignDataCrossesAsSystemVerilogChandle) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function chandle make_obj(input chandle parent);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  // The handle returned to SystemVerilog is a SystemVerilog type.
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kChandle);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  // The handle passed to the foreign side is likewise a SystemVerilog type.
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kChandle);
  EXPECT_FALSE(diag_.HasErrors());
}

}
