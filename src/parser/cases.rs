//! Case arms. [`Cases`] is the accumulator a `case` arm-list folds into: a [`CasesType`] tag
//! (`Nat` or `List`) plus the arms for each shape. Its building methods reject duplicate or
//! type-mixed arms (e.g. "duplicate zero case", "case mixes Nat and list patterns").

use super::stmt::Stmt;

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
    pub zk: Option<Box<Stmt>>,
    pub sk: Option<CasesNatSucc>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesNatSucc {
    pub var: String,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesList {
    pub nilk: Option<Box<Stmt>>,
    pub consk: Option<CasesListCons>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesListCons {
    pub x: String,
    pub xs: String,
    pub body: Box<Stmt>,
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

    pub fn set_nat_zero(&mut self, body: Stmt) -> Result<(), &'static str> {
        self.initialize_nat_case();
        if self.nat_case.as_ref().unwrap().zk.is_some() {
            return Err("duplicate zero case");
        }
        self.nat_case.as_mut().unwrap().zk = Some(Box::new(body));
        Ok(())
    }

    pub fn set_nat_succ(&mut self, var: String, body: Stmt) -> Result<(), &'static str> {
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

    pub fn set_list_nil(&mut self, body: Stmt) -> Result<(), &'static str> {
        self.initialize_list_case();
        if self.list_case.as_ref().unwrap().nilk.is_some() {
            return Err("duplicate nil case");
        }
        self.list_case.as_mut().unwrap().nilk = Some(Box::new(body));
        Ok(())
    }

    pub fn set_list_cons(&mut self, x: String, xs: String, body: Stmt) -> Result<(), &'static str> {
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
