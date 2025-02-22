#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::automata::{
        automaton::Automaton,
        automaton_builder::AutomatonBuilder,
        expressions::{Comparison, Expression},
        input_enabled::InputEnabled,
        literal::Literal,
        partitioned_symbol_table::PartitionedSymbolTable,
        refinement::Refinement,
        statements::Statement,
    };

    fn new_specification_tioa(symbols: PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(0, "u");

        let waiting = builder.add_location_with_name(0, "waiting");
        let slow = builder.add_location_with_name(0, "slow");
        let fast = builder.add_location(
            0,
            "fast",
            // u <= 20
            Expression::new_clock_constraint(
                Literal::new_identifier(clock).into(),
                Comparison::LessThanOrEqual,
                20.into(),
            ),
        );

        builder.set_initial_location(waiting);

        // if u > 2 and grant?
        builder.add_edge_input(
            0,
            waiting,
            slow,
            "grant",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::GreaterThan,
                2.into(),
            )),
            None,
        );

        // grant?
        builder.add_edge_input(0, slow, slow, "grant", None, None);

        // news!
        builder.add_edge_output(0, slow, slow, "news", None, None);

        // if u <= 2 and grant? then u := 0
        builder.add_edge_input(
            0,
            waiting,
            fast,
            "grant",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::LessThanOrEqual,
                2.into(),
            )),
            Some(Statement::Reset(clock, 0)),
        );

        // grant?
        builder.add_edge_input(0, fast, fast, "grant", None, None);

        // when news! then u := 0
        builder.add_edge_output(
            0,
            fast,
            waiting,
            "news",
            None,
            Some(Statement::Reset(clock, 0)),
        );

        builder.build().unwrap()
    }

    fn new_administration(symbols: PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(0, "z");

        let loc0 = builder.add_location_with_name(0, "admin_0");
        let loc1 = builder.add_location(
            0,
            "admin_1",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 2.into()),
        );
        let loc2 = builder.add_location(
            0,
            "admin_2",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 2.into()),
        );
        let loc3 = builder.add_location_with_name(0, "admin_3");
        builder.set_initial_location(loc0);

        // if grant? then z := 0
        builder.add_edge_input(
            0,
            loc0,
            loc1,
            "grant",
            None,
            Some(Statement::Reset(clock.into(), 0)),
        );

        // grant?, pub?
        builder.add_loop_input(0, loc1, "grant", None, None);
        builder.add_loop_input(0, loc1, "publication", None, None);

        // if pub? then z := 0
        builder.add_edge_input(
            0,
            loc0,
            loc2,
            "publication",
            None,
            Some(Statement::Reset(clock.into(), 0)),
        );

        // news!
        builder.add_edge_output(0, loc2, loc0, "news", None, None);

        // grant?, pub?
        builder.add_loop_input(0, loc2, "grant", None, None);
        builder.add_loop_input(0, loc2, "publication", None, None);

        // coin!
        builder.add_edge_output(0, loc1, loc3, "coin", None, None);

        // grant?
        builder.add_loop_input(0, loc3, "grant", None, None);

        // if pub? then z := 0
        builder.add_edge_input(
            0,
            loc3,
            loc2,
            "publication",
            None,
            Some(Statement::Reset(clock.into(), 0)),
        );

        builder.build().unwrap()
    }

    fn new_machine(symbols: PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(0, "y");

        let waiting = builder.add_location_with_name(0, "waiting");
        let serving = builder.add_location(
            0,
            "serving",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 6.into()),
        );

        builder.set_initial_location(waiting);

        // coin?
        builder.add_edge_input(0, serving, serving, "coin", None, None);

        // tea!
        builder.add_edge_output(0, serving, waiting, "tea", None, None);

        // if y >= 4 then coffee!
        builder.add_edge_output(
            0,
            serving,
            waiting,
            "coffee",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::GreaterThanOrEqual,
                4.into(),
            )),
            None,
        );

        // if y >= 2 then tea!
        builder.add_loop_output(
            0,
            waiting,
            "tea",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::GreaterThanOrEqual,
                2.into(),
            )),
            None,
        );

        // when coin? then y := 0
        builder.add_edge_input(
            0,
            waiting,
            serving,
            "coin",
            None,
            Some(Statement::Reset(clock, 0)),
        );

        builder.build().unwrap()
    }

    fn new_researcher(symbols: PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(0, "x");

        let loc0 = builder.add_location_with_name(0, "r_loc0");
        let loc1 = builder.add_location_with_name(0, "r_loc1");
        let loc2 = builder.add_location(
            0,
            "r_loc2",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 4.into()),
        );
        let loc3 = builder.add_location(
            0,
            "r_loc3",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 8.into()),
        );
        builder.set_initial_location(loc0);

        // if tea? and x > 15
        builder.add_edge_input(
            0,
            loc0,
            loc1,
            "tea",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::GreaterThan,
                15.into(),
            )),
            None,
        );

        // coffee?, tea?, pub!
        builder.add_loop_input(0, loc1, "coffee", None, None);
        builder.add_loop_input(0, loc1, "tea", None, None);
        builder.add_loop_output(0, loc1, "publication", None, None);

        // coffee?, tea?
        builder.add_loop_input(0, loc2, "coffee", None, None);
        builder.add_loop_input(0, loc2, "tea", None, None);

        // coffee?, tea?
        builder.add_loop_input(0, loc3, "coffee", None, None);
        builder.add_loop_input(0, loc3, "tea", None, None);

        // if coffee? then x := 0
        builder.add_edge_input(
            0,
            loc0,
            loc2,
            "coffee",
            None,
            Some(Statement::reset(clock, 0)),
        );

        // if x >= 2 when pub! then x := 0
        builder.add_edge_output(
            0,
            loc2,
            loc1,
            "publication",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::GreaterThanOrEqual,
                2.into(),
            )),
            Some(Statement::reset(clock, 0)),
        );

        // if x 1= 15 when tea? then x := 0
        builder.add_edge_input(
            0,
            loc0,
            loc3,
            "tea",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::LessThanOrEqual,
                15.into(),
            )),
            Some(Statement::reset(clock, 0)),
        );

        // if x >= 4 when pub! thn x := 0
        builder.add_edge_output(
            0,
            loc3,
            loc0,
            "publication",
            Some(Expression::new_clock_constraint(
                clock.into(),
                Comparison::GreaterThanOrEqual,
                4.into(),
            )),
            Some(Statement::reset(clock, 0)),
        );

        builder.build().unwrap()
    }

    #[test]
    fn specification() {
        let specification = new_specification_tioa(PartitionedSymbolTable::new());
        assert_eq!(specification.inputs().try_len().unwrap(), 1);
        assert_eq!(specification.outputs().try_len().unwrap(), 1);
        assert_eq!(specification.node_iter().try_len().unwrap(), 3);
        assert_eq!(specification.edge_iter().try_len().unwrap(), 6);
    }

    #[test]
    fn administration() {
        let administration = new_administration(PartitionedSymbolTable::new());
        assert_eq!(administration.inputs().try_len().unwrap(), 2);
        assert_eq!(administration.outputs().try_len().unwrap(), 2);
        assert_eq!(administration.node_iter().try_len().unwrap(), 4);
        assert_eq!(administration.edge_iter().try_len().unwrap(), 10);
    }

    #[test]
    fn machine() {
        let machine = new_machine(PartitionedSymbolTable::new());
        assert_eq!(machine.inputs().try_len().unwrap(), 1);
        assert_eq!(machine.outputs().try_len().unwrap(), 2);
        assert_eq!(machine.node_iter().try_len().unwrap(), 2);
        assert_eq!(machine.edge_iter().try_len().unwrap(), 5);
    }

    #[test]
    fn researcher() {
        let researcher = new_researcher(PartitionedSymbolTable::new());
        assert_eq!(researcher.inputs().try_len().unwrap(), 2);
        assert_eq!(researcher.outputs().try_len().unwrap(), 1);
        assert_eq!(researcher.node_iter().try_len().unwrap(), 4);
        assert_eq!(researcher.edge_iter().try_len().unwrap(), 12);
    }

    #[test]
    fn specification_refines_self() {
        let refinment = Refinement::new(
            new_specification_tioa(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
            new_specification_tioa(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines());
    }

    #[test]
    fn machine_refines_self() {
        let refinment = Refinement::new(
            new_machine(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
            new_machine(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines());
    }

    #[test]
    fn administration_refines_self() {
        let refinment = Refinement::new(
            new_administration(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
            new_administration(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines());
    }

    #[test]
    fn researcher_refines_self() {
        let refinment = Refinement::new(
            new_researcher(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
            new_researcher(PartitionedSymbolTable::new())
                .is_input_enabled()
                .unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines());
    }
}
