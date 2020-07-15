import .physlang


def worldGeometry := EuclideanGeometry  "worldGeometry" 3

def worldTime := ClassicalTime  "worldTime"  

def worldVelocity := ClassicalVelocity  "worldVelocity" 3



def REAL3.VAR.IDENTtf.start.point : Geometric3PointVar  :=  !58


def REAL1.EXPR.B.L105C36.E.L105C36 : Geometric3ScalarExpression  :=  ⬝(Geometric3ScalarDefault worldGeometry) 

def REAL1.EXPR.B.L105C40.E.L105C40 : Geometric3ScalarExpression  :=  ⬝(Geometric3ScalarDefault worldGeometry) 

def REAL1.EXPR.B.L105C44.E.L105C44 : Geometric3ScalarExpression  :=  ⬝(Geometric3ScalarDefault worldGeometry) 
def REAL3.EXPR.B.L105C26.E.L105C46 : Geometric3PointExpression  := (REAL1.EXPR.B.L105C36.E.L105C36) ⬝(REAL1.EXPR.B.L105C40.E.L105C40) ⬝(REAL1.EXPR.B.L105C44.E.L105C44) 
def STMT.B.L104C5.E.L105C47 : _ := (REAL3.VAR.IDENTtf.start.point)=(REAL3.EXPR.B.L105C26.E.L105C46)


def REAL3.VAR.IDENTtf.end.point : Geometric3PointVar  :=  !59


def REAL1.EXPR.B.L107C34.E.L107C34 : _ :=  ⬝. 

def REAL1.EXPR.B.L107C38.E.L107C39 : _ :=  ⬝. 

def REAL1.EXPR.B.L107C42.E.L107C42 : _ :=  ⬝. 
def REAL3.EXPR.B.L107C24.E.L107C44 : _ := (REAL1.EXPR.B.L107C34.E.L107C34)⬝(REAL1.EXPR.B.L107C38.E.L107C39)⬝(REAL1.EXPR.B.L107C42.E.L107C42)
def STMT.B.L106C5.E.L107C45 : _ := (REAL3.VAR.IDENTtf.end.point)=(REAL3.EXPR.B.L107C24.E.L107C44)


def REAL3.VAR.IDENTtf.displacement : Geometric3PointVar  :=  !60


def REAL3.EXPRtf.end.point.B.L109C35.E.L109C35 : _ := %(REAL3.VAR.IDENTtf.end.point)

def REAL3.EXPRtf.start.point.B.L109C50.E.L109C50 : _ := %(REAL3.VAR.IDENTtf.start.point)
def REAL3.EXPR.B.L109C35.E.L109C50 : _ := (REAL3.EXPRtf.end.point.B.L109C35.E.L109C35)-(REAL3.EXPRtf.start.point.B.L109C50.E.L109C50)
def STMT.B.L109C5.E.L109C64 : _ := (REAL3.VAR.IDENTtf.displacement)=(REAL3.EXPR.B.L109C35.E.L109C50)

