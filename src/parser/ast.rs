/// Function and lambda argument patterns
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Arg {
    Ident(String),
    Pair(Box<Arg>, Box<Arg>),
}

/// Types
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Arrow(Box<Type>, Box<Type>),
    Ident(String),
    List(Box<Type>),
    Product(Box<Type>, Box<Type>),
    Any,
}

/// Boolean expressions
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BExpr {
    Eq(Box<Expr>, Box<Expr>),
    NEq(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
}

/// Expressions: data and application, the control and constraint forms
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Zero,
    Succ(Box<Expr>),
    Nil,
    Cons(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    BExpr(BExpr),
    List(Vec<Expr>),
    Lambda(Arg, Box<Expr>),
    Ident(String),
    Nat(usize),
    Bool(bool),
    Pair(Box<Expr>, Box<Expr>),
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        r#else: Box<Expr>,
    },
    Let {
        var: String,
        val: Box<Expr>,
        body: Box<Expr>,
    },
    LetStrict {
        var: String,
        val: Box<Expr>,
        body: Box<Expr>,
    },
    Exists {
        var: String,
        r#type: Type,
        body: Box<Expr>,
    },
    Equate {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        body: Box<Expr>,
    },
    Choice(Vec<Expr>),
    Case {
        expr: Box<Expr>,
        cases: Cases,
    },
    Fail,
}

/// Top-level declarations
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    FuncType {
        name: String,
        r#type: Type,
    },
    Func {
        name: String,
        args: Vec<Arg>,
        body: Expr,
    },
    Expr(Expr),
}

/// Case arms: the accumulator a `case` arm-list folds into. Its building methods reject duplicate
/// or type-mixed arms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cases {
    pub r#type: Option<CasesType>,
    pub nat_case: Option<CasesNat>,
    pub list_case: Option<CasesList>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CasesType {
    Nat,
    List,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesNat {
    pub zk: Option<Box<Expr>>,
    pub sk: Option<CasesNatSucc>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesNatSucc {
    pub var: String,
    pub body: Box<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesList {
    pub nilk: Option<Box<Expr>>,
    pub consk: Option<CasesListCons>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesListCons {
    pub x: String,
    pub xs: String,
    pub body: Box<Expr>,
}

impl Default for Cases {
    fn default() -> Self {
        Self::new()
    }
}

impl Cases {
    pub fn new() -> Self {
        Cases {
            r#type: None,
            nat_case: None,
            list_case: None,
        }
    }

    fn initialize_nat_case(&mut self) {
        if self.nat_case.is_none() {
            self.nat_case = Some(CasesNat::new());
        }
    }

    fn initialize_list_case(&mut self) {
        if self.list_case.is_none() {
            self.list_case = Some(CasesList::new());
        }
    }

    pub fn set_type_or_check(&mut self, r#type: CasesType) -> Result<(), &'static str> {
        if let Some(t) = &self.r#type {
            if *t != r#type {
                return Err("case mixes Nat and list patterns");
            }
        } else {
            self.r#type = Some(r#type);
        }
        Ok(())
    }

    pub fn set_nat_zero(&mut self, body: Expr) -> Result<(), &'static str> {
        self.initialize_nat_case();
        if self.nat_case.as_ref().unwrap().zk.is_some() {
            return Err("duplicate zero case");
        }
        self.nat_case.as_mut().unwrap().zk = Some(Box::new(body));
        Ok(())
    }

    pub fn set_nat_succ(&mut self, var: String, body: Expr) -> Result<(), &'static str> {
        self.initialize_nat_case();
        if self.nat_case.as_ref().unwrap().sk.is_some() {
            return Err("duplicate successor case");
        }
        self.nat_case.as_mut().unwrap().sk = Some(CasesNatSucc {
            var,
            body: Box::new(body),
        });
        Ok(())
    }

    pub fn set_list_nil(&mut self, body: Expr) -> Result<(), &'static str> {
        self.initialize_list_case();
        if self.list_case.as_ref().unwrap().nilk.is_some() {
            return Err("duplicate nil case");
        }
        self.list_case.as_mut().unwrap().nilk = Some(Box::new(body));
        Ok(())
    }

    pub fn set_list_cons(&mut self, x: String, xs: String, body: Expr) -> Result<(), &'static str> {
        self.initialize_list_case();
        if self.list_case.as_ref().unwrap().consk.is_some() {
            return Err("duplicate cons case");
        }
        self.list_case.as_mut().unwrap().consk = Some(CasesListCons {
            x,
            xs,
            body: Box::new(body),
        });
        Ok(())
    }
}

impl CasesNat {
    fn new() -> Self {
        CasesNat { zk: None, sk: None }
    }
}

impl CasesList {
    fn new() -> Self {
        CasesList {
            nilk: None,
            consk: None,
        }
    }
}
