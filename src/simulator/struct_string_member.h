#pragma once

#include "common/types.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;

Logic4Vec StringMemberHandle(const Logic4Vec& text, Arena& arena);

Logic4Vec StringMemberText(const Logic4Vec& handle, Arena& arena);

Logic4Vec MemberBitsOf(const Logic4Vec& val, DataTypeKind kind, Arena& arena);

Logic4Vec MemberValueOf(const Logic4Vec& bits, DataTypeKind kind, Arena& arena);

}  // namespace delta
