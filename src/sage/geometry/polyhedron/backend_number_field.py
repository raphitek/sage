r"""
The Python backend, using number fields internally
"""

# ****************************************************************************
#  Copyright (C) 2016-2022 Matthias Köppe <mkoeppe at math.ucdavis.edu>
#                2016-2018 Travis Scrimshaw
#                2017      Jeroen Demeyer
#                2018-2020 Jean-Philippe Labbé
#                2019      Vincent Delecroix
#                2019-2021 Jonathan Kliem
#                2019-2021 Sophia Elia
#                2020      Frédéric Chapoton
#                2022      Yuan Zhou
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from .backend_field import Polyhedron_field
from .base_number_field import Polyhedron_base_number_field


class Polyhedron_number_field(Polyhedron_field, Polyhedron_base_number_field):
    r"""
    Polyhedra whose data can be converted to number field elements

    All computations are done internally using a fixed real embedded number field,
    which is determined automatically.

    INPUT:

    - ``Vrep`` -- a list ``[vertices, rays, lines]`` or ``None``.

    - ``Hrep`` -- a list ``[ieqs, eqns]`` or ``None``.

    EXAMPLES:

    TODO --- examples where input is in SR. Can copy from backend_normaliz.


    TESTS:

    Tests from backend_field -- here the data are already either in a number field or in AA.

        sage: p = Polyhedron(vertices=[(0,0),(AA(2).sqrt(),0),(0,AA(3).sqrt())],            # optional - sage.rings.number_field
        ....:                rays=[(1,1)], lines=[], backend='number_field', base_ring=AA)
        sage: TestSuite(p).run()                                                            # optional - sage.rings.number_field

        sage: K.<sqrt3> = QuadraticField(3)                                                 # optional - sage.rings.number_field
        sage: p = Polyhedron([(0,0), (1,0), (1/2, sqrt3/2)], backend='number_field')        # optional - sage.rings.number_field
        sage: TestSuite(p).run()                                                            # optional - sage.rings.number_field

    Check that :trac:`19013` is fixed::

        sage: K.<phi> = NumberField(x^2-x-1, embedding=1.618)                               # optional - sage.rings.number_field
        sage: P1 = Polyhedron([[0,1], [1,1], [1,-phi+1]], backend='number_field')           # optional - sage.rings.number_field
        sage: P2 = Polyhedron(ieqs=[[-1,-phi,0]], backend='number_field')                   # optional - sage.rings.number_field
        sage: P1.intersection(P2)                                                           # optional - sage.rings.number_field
        The empty polyhedron in (Number Field in phi with defining polynomial x^2 - x - 1 with phi = 1.618033988749895?)^2

    Check that :trac:`28654` is fixed::

        sage: Polyhedron(lines=[[1]], backend='number_field')
        A 1-dimensional polyhedron in QQ^1 defined as the convex hull of 1 vertex and 1 line
    """

    def _init_from_Vrepresentation(self, vertices, rays, lines,
                                   minimize=True, verbose=False):
        """
        Construct polyhedron from V-representation data.

        INPUT:

        - ``vertices`` -- list of points. Each point can be specified
           as any iterable container of
           :meth:`~sage.geometry.polyhedron.base.base_ring` elements.

        - ``rays`` -- list of rays. Each ray can be specified as any
          iterable container of
          :meth:`~sage.geometry.polyhedron.base.base_ring` elements.

        - ``lines`` -- list of lines. Each line can be specified as
          any iterable container of
          :meth:`~sage.geometry.polyhedron.base.base_ring` elements.

        - ``verbose`` -- boolean (default: ``False``). Whether to print
          verbose output for debugging purposes.

        EXAMPLES::

            sage: p = Polyhedron(ambient_dim=2, backend='number_field')
            sage: from sage.geometry.polyhedron.backend_number_field import Polyhedron_number_field
            sage: Polyhedron_number_field._init_from_Vrepresentation(p, [(0,0)], [], [])
        """
        # TODO: Transform data
        super()._init_from_Vrepresentation(vertices, rays, lines,
                                           minimize=minimize, verbose=verbose)

    def _init_from_Hrepresentation(self, ieqs, eqns, minimize=True, verbose=False):
        """
        Construct polyhedron from H-representation data.

        INPUT:

        - ``ieqs`` -- list of inequalities. Each line can be specified
          as any iterable container of
          :meth:`~sage.geometry.polyhedron.base.base_ring` elements.

        - ``eqns`` -- list of equalities. Each line can be specified
          as any iterable container of
          :meth:`~sage.geometry.polyhedron.base.base_ring` elements.

        - ``verbose`` -- boolean (default: ``False``). Whether to print
          verbose output for debugging purposes.

        TESTS::

            sage: p = Polyhedron(ambient_dim=2, backend='number_field')
            sage: from sage.geometry.polyhedron.backend_number_field import Polyhedron_number_field
            sage: Polyhedron_number_field._init_from_Hrepresentation(p, [(1, 2, 3)], [])
        """
        # TODO: Transform data
        super()._init_from_Hrepresentation(ieqs, eqns, minimize=minimize, verbose=verbose)
