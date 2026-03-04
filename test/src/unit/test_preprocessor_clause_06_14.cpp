#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, ChandleInClass) {

  auto r = ParseWithPreprocessor(
      "class Wrapper;\n"
      "  chandle ptr;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->data_type.kind,
            DataTypeKind::kChandle);
}

}
