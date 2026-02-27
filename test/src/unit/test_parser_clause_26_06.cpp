// §26.6: Exporting imported names from packages

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA213, PackageExportMultipleItems) {
  // BNF: export package_import_item { , package_import_item } ;
  auto r = Parse(
      "package pkg;\n"
      "  export p1::a, p2::b;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int export_count = 0;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) export_count++;
  }
  EXPECT_GE(export_count, 2);
}

}  // namespace
