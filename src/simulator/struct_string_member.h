#pragma once

#include "common/types.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;

// §7.2 with §6.16: a string member of an unpacked structure is a string
// variable, of any length, so the structure's packed value holds a handle to
// the member's text (kStringMemberHandleWidth bits) rather than the text. The
// text a handle names never changes -- a write to the member takes a new
// handle -- so a copy of the structure copies its strings with the handle,
// and equal texts share one handle, so structures holding equal strings
// compare equal.

// The handle naming `text`, a string value.
Logic4Vec StringMemberHandle(const Logic4Vec& text, Arena& arena);

// The string value the handle `handle` names: the text StringMemberHandle
// gave it for, and the empty string for the zero handle, which a member never
// written holds, and for one with an unknown bit (§11.9).
Logic4Vec StringMemberText(const Logic4Vec& handle, Arena& arena);

// The bits a member of the declared type `kind` holds for the value `val`
// written to it: a string member's handle, and `val` itself for any other.
Logic4Vec MemberBitsOf(const Logic4Vec& val, DataTypeKind kind, Arena& arena);

// The value a member of the declared type `kind` reads as from the bits it
// holds: a string member's text, and `bits` themselves for any other.
Logic4Vec MemberValueOf(const Logic4Vec& bits, DataTypeKind kind, Arena& arena);

}  // namespace delta
