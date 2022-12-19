# Futhark - A Runes Implementation in Rust

This is a rust implementation of the original runes library by *Rusty Russell* [https://github.com/rustyrussell/runes](https://github.com/rustyrussell/runes).

## What are Runes?

Runes are extendable authorization cookies, similar to **Macaroons** [https://research.google/pubs/pub41892/](https://research.google/pubs/pub41892/) but simpler. Extendable meaning that a client that has access to a cookie issued by a server can derive a cookie with extra restrictions that can not be removed from the derived cookie. This cookie can then possibly be passed to some other party to authenticate at the server.

To find out more about the motivation of runes see the original repository.

## Coverage and Features

This implementation is fully compliant with the given set of test vectors. However, a clean implementation of functional values for alternatives to check on are currently missing. These will be part of a future update.

- [x] Compliant with test vectors
- [ ] Functional checks on values
- [ ] Full crate documentation

## Rune Language
(See the original repository for an in-depth explanation)

A _rune_ is a set of _restrictions_ that have to be passed. A _restriction_ consists of one or more _alternatives_ where at least one _alternative_ has to pass.

### Alternative

An _alternative_ is a string of the form (no spaces):
```
ALTERNATIVE := FIELDNAME CONDITION VALUE
```

`FIELDNAME` contains only UTF-8 characters excluding punctuation characters:

```
! " # $ % & ' ( ) * +, - . / : ; < = > ? @ [ \ ] ^ _ \` { | } ~
```
Still, the punctuation characters can appear inside a `VALUE` but `&`, `|` and `\\` must be escaped with `\`, as these are used to separate _alternatives_ and _restrictions_.

`CONDITION` is one of the following values with the corresponding check
| `CONDITION` | check                                                                  |
| ----------- | ---------------------------------------------------------------------- |
| `!`         | field is missing                                                       |
| `=`         | exists and exactly equals                                              |
| `/`         | exists and is not exactly equal                                        |
| `^`         | exists and begins with                                                 |
| `$`         | exists and ends with                                                   |
| `~`         | exists and contains                                                    |
| `<`         | exists, is valid integer (may be signed), and numerically less than    |
| `>`         | exists, is valid integer (may be signed), and numerically greater than |
| `{`         | exists and lexicographically less than (or shorter)                    |
| `}`         | exists and lexicographically greater than (or longer)                  |
| `#`         | comment (always pass)                                                  |

### Restriction

A _restriction_ is a group of _alternatives_ chained by a logically `OR` condition represented by `|`; _restrictions_ are separated by `&`. Example _rune_:
```
cmd=foo|cmd=bar&subcmd!|subcmd={get
```
The first _restriction_ requires `cmd` to be `foo` or `bar`, the second requires that `subcmd` is not present, or is lexicographically less than (or shorter) `get`.

## Rune Authorization
Every rune comes with a __SHA-256__ authentication code that ensures that no _restriction_ can be striped from the rune. The basis for every `authcode` is a secret (less than 56 bytes), that is only known by the server that issues the rune.

From this `authbase` every _restriction_ is appended to a rune with the following update to the `authcode`, assuming that the secret has been treated the same way:
 - Pad the _restriction_ (the secret for the `authbase`) as per SHA-256 such that the result is a multiple of 64:
    - append `0x80`.
    - append `0`s (such that the result is a multiple of 64).
    - append the big-endian 64-bit bitcount (len) of the _restriction_.

This way, the `authcode` is always a SHA-256 digest.

A derivation is then achieved by adding a new restriction to the rune and updating the `authcode`.

### Encoding

_Runes_ are _base64_ encoded (URL safe), starting with the SHA-256 `authcode`, followed by the restrictions (one or more) separated by `&`.


## More

For more insights additional infos and examples visit the original repo [https://github.com/rustyrussell/runes](https://github.com/rustyrussell/runes).


