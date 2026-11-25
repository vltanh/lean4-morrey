#!/usr/bin/env python3
"""Generate and check one exact nonconvex-but-RC control and rejection cases."""

from pathlib import Path
from fractions import Fraction as F
import copy
import json
from sphere_certificate import add,mul,variable,ZERO,encode,verify,norm_gram_basis


def main():
    out = Path(__file__).parent
    one = {ZERO:F(1)}
    s = {}
    for i in range(1,5):s = add(s,mul(variable(i),variable(i)))
    determinant = add(mul(variable(1),variable(4)),mul(variable(2),variable(3)),F(-1))
    p = add(mul(add(one,s),add(one,s)),determinant,F(5))
    integrand = {e[1:5]:c for e,c in p.items()}
    inner = {}
    for i in range(2):
        for j in range(2):
            inner = add(inner,mul(mul(variable(1+2*i+j),variable(5+i)),variable(7+j)))
    nu = add(mul(variable(5),variable(5)),mul(variable(6),variable(6)))
    nv = add(mul(variable(7),variable(7)),mul(variable(8),variable(8)))
    data = {'schema_version':1,'matrix_shape':[2,2],'degree_bound':4,
            'variables':['t','a','b','c','d','u0','u1','v0','v1'],
            'integrand':encode(integrand),'epsilon':'2',
            'squares':[{'weight':'8','polynomial':encode(inner)},
                       {'weight':'2','polynomial':encode(one)}],
            'sphere_multipliers':[encode({e:-4*c for e,c in mul(nu,nv).items()}),
                                  encode({e:-4*c for e,c in nv.items()}),
                                  encode({ZERO:F(-4)})],
            'witness':{'base':[0,0,0,0],
                       'nodes':[[[0,0],[1,0]],[[0,1],[0,0]]]},
            'comment':'f(A)=(1+|A|²)²+5det A. Hessian at zero in diag(1,-1) is -2, so f is not convex. This is a control, not a Morrey counterexample.'}
    control = out/'sphere_control_certificate.json'
    control.write_text(json.dumps(data,indent=2)+'\n')
    results = {'valid_control':verify(data),'rejections':[]}
    nx=add(mul(variable(0),variable(0)),s)
    norm=mul(mul(nx,nu),nv)
    weighted=copy.deepcopy(data)
    weighted['certificate_kind']='norm_multiplier';weighted['multiplier_order']=1
    weighted.pop('sphere_multipliers')
    weighted['squares']=[{'weight':'2','polynomial':encode(norm)}]
    for i in range(5):
        for j in range(5,7):
            for k in range(7,9):
                monomial=mul(mul(variable(i),variable(j)),variable(k))
                weighted['squares'].append({'weight':'8','polynomial':encode(mul(inner,monomial))})
    (out/'norm_control_certificate.json').write_text(json.dumps(weighted,indent=2)+'\n')
    results['norm_multiplier_control']=verify(weighted)
    results['quartic_order_one_gram_size']=len(norm_gram_basis(4,1))
    results['sextic_order_one_gram_size']=len(norm_gram_basis(6,1))
    assert results['quartic_order_one_gram_size']==135
    assert results['sextic_order_one_gram_size']==315
    # Constants/affine terms do not affect LH: change the a^4 term instead.
    tests=[]
    for kind,original in [('sphere_ideal',data),('norm_multiplier',weighted)]:
        bad=copy.deepcopy(original)
        for term in bad['integrand']:
            if term['exponents']==[4,0,0,0]:term['coefficient']='-10'
        tests.append((kind+':changed_curvature',bad))
        bad=copy.deepcopy(original);bad['squares'][0]['weight']='-8'
        tests.append((kind+':negative_square_weight',bad))
        bad=copy.deepcopy(original);bad['epsilon']='0'
        tests.append((kind+':zero_margin',bad))
    for name,candidate in tests:
        try:verify(candidate)
        except ValueError as error:results['rejections'].append({'case':name,'reason':str(error)})
        else:raise AssertionError(name+' was not rejected')
    (out/'sphere_control_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))


if __name__=='__main__':main()
