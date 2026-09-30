//! A minimal JSON reader, enough for tests.json (non-negative integers only, BMP `\u` escapes only).
//! Kept dependency-free so the reference builds without network access.

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(u64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(fields) => fields.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn field(&self, key: &str) -> &Json {
        self.get(key).unwrap_or_else(|| panic!("missing field {key:?} in {self:?}"))
    }
    pub fn num(&self) -> u64 {
        match self {
            Json::Num(n) => *n,
            _ => panic!("expected a number, found {self:?}"),
        }
    }
    pub fn str(&self) -> &str {
        match self {
            Json::Str(s) => s,
            _ => panic!("expected a string, found {self:?}"),
        }
    }
    pub fn arr(&self) -> &[Json] {
        match self {
            Json::Arr(a) => a,
            _ => panic!("expected an array, found {self:?}"),
        }
    }
    /// `null` is None, a number `w` is Some(w).
    pub fn opt_num(&self) -> Option<u64> {
        match self {
            Json::Null => None,
            j => Some(j.num()),
        }
    }
}

pub fn parse(src: &str) -> Json {
    let mut p = Parser { s: src.as_bytes(), i: 0 };
    let v = p.value();
    p.ws();
    assert!(p.i == p.s.len(), "trailing input at byte {}", p.i);
    v
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl Parser<'_> {
    fn ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }
    fn eat(&mut self, c: u8) {
        self.ws();
        assert!(self.s.get(self.i) == Some(&c), "expected {:?} at byte {}", c as char, self.i);
        self.i += 1;
    }
    fn peek(&mut self) -> u8 {
        self.ws();
        *self.s.get(self.i).expect("unexpected end of input")
    }
    fn lit(&mut self, word: &str, v: Json) -> Json {
        assert!(self.s[self.i..].starts_with(word.as_bytes()), "bad literal at byte {}", self.i);
        self.i += word.len();
        v
    }
    fn value(&mut self) -> Json {
        match self.peek() {
            b'n' => self.lit("null", Json::Null),
            b't' => self.lit("true", Json::Bool(true)),
            b'f' => self.lit("false", Json::Bool(false)),
            b'"' => Json::Str(self.string()),
            b'[' => {
                self.eat(b'[');
                let mut items = Vec::new();
                if self.peek() == b']' {
                    self.i += 1;
                    return Json::Arr(items);
                }
                loop {
                    items.push(self.value());
                    match self.peek() {
                        b',' => self.i += 1,
                        b']' => {
                            self.i += 1;
                            return Json::Arr(items);
                        }
                        c => panic!("unexpected {:?} in array at byte {}", c as char, self.i),
                    }
                }
            }
            b'{' => {
                self.eat(b'{');
                let mut fields = Vec::new();
                if self.peek() == b'}' {
                    self.i += 1;
                    return Json::Obj(fields);
                }
                loop {
                    self.ws();
                    let k = self.string();
                    self.eat(b':');
                    fields.push((k, self.value()));
                    match self.peek() {
                        b',' => self.i += 1,
                        b'}' => {
                            self.i += 1;
                            return Json::Obj(fields);
                        }
                        c => panic!("unexpected {:?} in object at byte {}", c as char, self.i),
                    }
                }
            }
            b'0'..=b'9' => {
                let start = self.i;
                while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
                    self.i += 1;
                }
                let text = std::str::from_utf8(&self.s[start..self.i]).unwrap();
                Json::Num(text.parse().expect("number out of u64 range"))
            }
            c => panic!("unexpected {:?} at byte {}", c as char, self.i),
        }
    }
    fn string(&mut self) -> String {
        self.eat(b'"');
        let mut out = Vec::new();
        loop {
            let c = *self.s.get(self.i).expect("unterminated string");
            self.i += 1;
            match c {
                b'"' => return String::from_utf8(out).expect("invalid UTF-8"),
                b'\\' => {
                    let e = self.s[self.i];
                    self.i += 1;
                    match e {
                        b'"' | b'\\' | b'/' => out.push(e),
                        b'n' => out.push(b'\n'),
                        b't' => out.push(b'\t'),
                        b'u' => {
                            let hex = std::str::from_utf8(&self.s[self.i..self.i + 4]).unwrap();
                            self.i += 4;
                            let ch = char::from_u32(u32::from_str_radix(hex, 16).unwrap()).expect("surrogate escapes unsupported");
                            out.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes());
                        }
                        _ => panic!("unsupported escape \\{}", e as char),
                    }
                }
                _ => out.push(c),
            }
        }
    }
}
