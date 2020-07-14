import .physlang


def worldGeometry := EuclideanGeometry  "worldGeometry" 3

def worldTime := ClassicalTime  "worldTime"  

def worldVelocity := ClassicalVelocity  "worldVelocity" 3



def REAL3_VAR_IDENT_tf_start_point : Geometric3PointVar  :=  !1


def REAL1.LITERAL.B.L105C36.E.L105C36 : _ :=  GeometricScalarExpression.GeometricScalarLiteral 1

def REAL1.LITERAL.B.L105C40.E.L105C40 : _ :=  %_ 

def REAL1.LITERAL.B.L105C44.E.L105C44 : GeometricScalarExpression  :=  %GeometricScalarDefault 
def REAL3.LITERAL.B.L105C26.E.L105C46 : _ := % (REAL1.EXPR.B.L105C36.E.L105C36)  (REAL1.EXPR_.B.L105C40.E.L105C40)  (REAL1.EXPR.B.L105C44.E.L105C44) 
def DECLARE.B.L104C5.E.L105C47 : _ := (REAL3.VAR.IDENT.tf.start.point) = (REAL3.EXPR_.B.L105C26.E.L105C46)


def REAL3.VAR.IDENT.tf.end.point : Geometric3PointVar  :=  !2


def REAL1.LITERAL.B.L107C34.E.L107C34 : _ :=  %_ 

def REAL1.LITERAL.B.L107C38.E.L107C39 : _ :=  %_ 

def REAL1.LITERAL.B.L107C42.E.L107C42 : _ :=  %_ 
def REAL3.LITERAL.B.L107C24.E.L107C44 : _ := % (REAL1.EXPR_.B.L107C34.E.L107C34)  (REAL1.EXPR_.B.L107C38.E.L107C39)  (REAL1.EXPR.B.L107C42.E.L107C42) 
def DECLARE.B.L106C5.E.L107C45 : _ := (REAL3.VAR.IDENT.tf.end.point) = (REAL3.EXPR_.B.L107C24.E.L107C44)


def REAL3_VAR_IDENT_tf_displacement : GeometricVectorVar  :=  !3


def REAL3.EXPR_tf_end_point.B.L109C35.E.L109C35 : _ := # (REAL3.VAR.IDENT.tf.end.point) 

def REAL3.EXPR_tf_start_point.B.L109C50.E.L109C50 : _ := # (REAL3.VAR.IDENT.tf.start.point) 
def REAL3.EXPR_.B.L109C35.E.L109C50 : _ := (REAL3.EXPR_tf_end_point.B.L109C35.E.L109C35) - (REAL3.EXPR_tf_start_point.B.L109C50.E.L109C50)
def DECLARE_.B.L109C5.E.L109C64 : _ := (REAL3.VAR.IDENT.tf.displacement) = (REAL3.EXPR_.B.L109C35.E.L109C50)

