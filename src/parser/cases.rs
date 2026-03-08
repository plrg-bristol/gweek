use super::stmt::Stmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cases {
    pub r#type: Option<CasesType>,
    pub nat_case: Option<CasesNat>,
    pub list_case: Option<CasesList>
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CasesType { Nat, List }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesNat {
    pub zk: Option<Box<Stmt>>,
    pub sk: Option<CasesNatSucc>
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesNatSucc {
    pub var: String,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesList {
    pub nilk: Option<Box<Stmt>>,
    pub consk: Option<CasesListCons>
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CasesListCons {
    pub x: String,
    pub xs: String,
    pub body: Box<Stmt>
}

impl Cases {
    pub fn new() -> Self {
        Cases { r#type: None, nat_case: None, list_case: None }
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

    pub fn set_type_or_check(&mut self, r#type: CasesType) {
        if self.r#type.is_some() {
            let t = self.r#type.as_mut().unwrap();
            if *t != r#type { panic!("bad cases") }
        } else {
            self.r#type = Some(r#type);
        }
    }

    pub fn set_nat_zero(&mut self, body: Stmt) {
        self.initialize_nat_case();
        if self.nat_case.as_ref().unwrap().zk.is_some() { panic!("zero case already set") }
        self.nat_case.as_mut().unwrap().zk = Some(Box::new(body));
    }

    pub fn set_nat_succ(&mut self, var: String, body: Stmt) {
        self.initialize_nat_case();
        if self.nat_case.as_ref().unwrap().sk.is_some() { panic!("succ case already set") }
        self.nat_case.as_mut().unwrap().sk = Some(CasesNatSucc { var, body: Box::new(body) })
    }

    pub fn set_list_nil(&mut self, body: Stmt) {
        self.initialize_list_case();
        if self.list_case.as_ref().unwrap().nilk.is_some() { panic!("nil case already set") }
        self.list_case.as_mut().unwrap().nilk = Some(Box::new(body));
    }

    pub fn set_list_cons(&mut self, x: String, xs: String, body: Stmt) {
        self.initialize_list_case();
        if self.list_case.as_ref().unwrap().consk.is_some() { panic!("cons case already set") }
        self.list_case.as_mut().unwrap().consk = Some(CasesListCons { x, xs, body: Box::new(body) })
    }
}

impl CasesNat {
    fn new() -> Self {
        CasesNat { zk: None, sk: None }
    }
}

impl CasesList {
    fn new() -> Self {
        CasesList { nilk: None, consk: None }
    }
}
