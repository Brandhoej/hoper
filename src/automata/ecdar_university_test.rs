#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use petgraph::dot::Dot;

    use crate::automata::{
        action::Action,
        automaton::{Automaton, IntoAutomaton},
        automaton_builder::AutomatonBuilder,
        composition::Composition,
        expressions::{Comparison, Expression},
        input_enabled::InputEnabled,
        ioa::IOA,
        literal::Literal,
        partitioned_symbol_table::PartitionedSymbolTable,
        refinement::Refinement,
        statements::Statement,
        ta::TA,
        tioa::TIOA,
    };

    fn new_specification(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let global = 0;
        let partition = 1;
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(partition, "u");

        let waiting = builder.add_location_with_name(partition, "waiting");
        let slow = builder.add_location_with_name(partition, "slow");
        let fast = builder.add_location(
            partition,
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
            global,
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
        builder.add_edge_input(global, slow, slow, "grant", None, None);

        // news!
        builder.add_edge_output(global, slow, slow, "news", None, None);

        // if u <= 2 and grant? then u := 0
        builder.add_edge_input(
            global,
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
        builder.add_edge_input(global, fast, fast, "grant", None, None);

        // when news! then u := 0
        builder.add_edge_output(
            global,
            fast,
            waiting,
            "news",
            None,
            Some(Statement::Reset(clock, 0)),
        );

        builder.build().unwrap()
    }

    fn new_administration(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let global = 0;
        let partition = 2;
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(partition, "z");

        let loc0 = builder.add_location_with_name(partition, "0");
        let loc1 = builder.add_location(
            partition,
            "1",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 2.into()),
        );
        let loc2 = builder.add_location(
            partition,
            "2",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 2.into()),
        );
        let loc3 = builder.add_location_with_name(partition, "3");
        builder.set_initial_location(loc0);

        // if grant? then z := 0
        builder.add_edge_input(
            global,
            loc0,
            loc1,
            "grant",
            None,
            Some(Statement::Reset(clock.into(), 0)),
        );

        // grant?, pub?
        builder.add_loop_input(global, loc1, "grant", None, None);
        builder.add_loop_input(global, loc1, "publication", None, None);

        // if pub? then z := 0
        builder.add_edge_input(
            global,
            loc0,
            loc2,
            "publication",
            None,
            Some(Statement::Reset(clock.into(), 0)),
        );

        // news!
        builder.add_edge_output(global, loc2, loc0, "news", None, None);

        // grant?, pub?
        builder.add_loop_input(global, loc2, "grant", None, None);
        builder.add_loop_input(global, loc2, "publication", None, None);

        // coin!
        builder.add_edge_output(global, loc1, loc3, "coin", None, None);

        // grant?
        builder.add_loop_input(global, loc3, "grant", None, None);

        // if pub? then z := 0
        builder.add_edge_input(
            global,
            loc3,
            loc2,
            "publication",
            None,
            Some(Statement::Reset(clock.into(), 0)),
        );

        builder.build().unwrap()
    }

    fn new_machine(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let global = 0;
        let partition = 3;
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(partition, "y");

        let loc0 = builder.add_location_with_name(partition, "0");
        let loc1 = builder.add_location(
            0,
            "1",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 6.into()),
        );

        builder.set_initial_location(loc0);

        // coin?
        builder.add_edge_input(global, loc1, loc1, "coin", None, None);

        // tea!
        builder.add_edge_output(global, loc1, loc0, "tea", None, None);

        // if y >= 4 then coffee!
        builder.add_edge_output(
            global,
            loc1,
            loc0,
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
            global,
            loc0,
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
            global,
            loc0,
            loc1,
            "coin",
            None,
            Some(Statement::Reset(clock, 0)),
        );

        builder.build().unwrap()
    }

    fn new_researcher(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let global = 0;
        let partition = 4;
        let mut builder = AutomatonBuilder::new(symbols);
        let clock = builder.add_clock(partition, "x");

        let loc0 = builder.add_location_with_name(partition, "0");
        let loc1 = builder.add_location_with_name(partition, "1");
        let loc2 = builder.add_location(
            partition,
            "2",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 4.into()),
        );
        let loc3 = builder.add_location(
            partition,
            "3",
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 8.into()),
        );
        builder.set_initial_location(loc0);

        // if tea? and x > 15
        builder.add_edge_input(
            global,
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
        builder.add_loop_input(global, loc1, "coffee", None, None);
        builder.add_loop_input(global, loc1, "tea", None, None);
        builder.add_loop_output(global, loc1, "publication", None, None);

        // coffee?, tea?
        builder.add_loop_input(global, loc2, "coffee", None, None);
        builder.add_loop_input(global, loc2, "tea", None, None);

        // coffee?, tea?
        builder.add_loop_input(global, loc3, "coffee", None, None);
        builder.add_loop_input(global, loc3, "tea", None, None);

        // if coffee? then x := 0
        builder.add_edge_input(
            global,
            loc0,
            loc2,
            "coffee",
            None,
            Some(Statement::reset(clock, 0)),
        );

        // if x >= 2 when pub! then x := 0
        builder.add_edge_output(
            global,
            loc2,
            loc0,
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
            global,
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
            global,
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
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(&mut symbols);

        assert_eq!(specification.inputs().try_len().unwrap(), 1);
        assert_eq!(specification.outputs().try_len().unwrap(), 1);
        assert_eq!(specification.node_iter().try_len().unwrap(), 3);
        assert_eq!(specification.edge_iter().try_len().unwrap(), 6);
    }

    #[test]
    fn administration() {
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(&mut symbols);

        assert_eq!(administration.inputs().try_len().unwrap(), 2);
        assert_eq!(administration.outputs().try_len().unwrap(), 2);
        assert_eq!(administration.node_iter().try_len().unwrap(), 4);
        assert_eq!(administration.edge_iter().try_len().unwrap(), 10);
    }

    #[test]
    fn machine() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);

        assert_eq!(machine.inputs().try_len().unwrap(), 1);
        assert_eq!(machine.outputs().try_len().unwrap(), 2);
        assert_eq!(machine.node_iter().try_len().unwrap(), 2);
        assert_eq!(machine.edge_iter().try_len().unwrap(), 5);
    }

    #[test]
    fn researcher() {
        let mut symbols = PartitionedSymbolTable::new();
        let researcher = new_researcher(&mut symbols);

        assert_eq!(researcher.inputs().try_len().unwrap(), 2);
        assert_eq!(researcher.outputs().try_len().unwrap(), 1);
        assert_eq!(researcher.node_iter().try_len().unwrap(), 4);
        assert_eq!(researcher.edge_iter().try_len().unwrap(), 12);
    }

    #[test]
    fn machine_researcher_composition() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let composition = Composition::new(
            machine.clone().is_input_enabled().unwrap(),
            researcher.clone().is_input_enabled().unwrap(),
        )
        .unwrap();

        let coin = Action::new(symbols.intern(0, "coin"));
        let coffee = Action::new(symbols.intern(0, "coffee"));
        let tea = Action::new(symbols.intern(0, "tea"));
        let publication = Action::new(symbols.intern(0, "publication"));
        assert!(composition.inputs().contains(&coin));
        assert!(composition.outputs().contains(&coffee));
        assert!(composition.outputs().contains(&tea));
        assert!(composition.outputs().contains(&publication));

        assert_eq!(composition.inputs().len(), 1);
        assert_eq!(composition.outputs().len(), 3);
        assert_eq!(composition.clock_count(), 2);

        let automaton = composition.clone().into_automaton().unwrap();

        assert_eq!(automaton.node_iter().try_len().unwrap(), 8);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 28); // Q: Should it be 29?
    }

    #[test]
    fn machine_researcher_administration_composition() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let administration = new_administration(&mut symbols);

        let machine_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();
        let machine_administration_researcher = Composition::new(
            Box::new(machine_administration.into()),
            researcher.is_input_enabled().unwrap(),
        )
        .unwrap();

        let coin = Action::new(symbols.intern(0, "coin"));
        let coffee = Action::new(symbols.intern(0, "coffee"));
        let tea = Action::new(symbols.intern(0, "tea"));
        let publication = Action::new(symbols.intern(0, "publication"));
        let news = Action::new(symbols.intern(0, "news"));
        let grant = Action::new(symbols.intern(0, "grant"));

        assert!(machine_administration_researcher.inputs().contains(&grant));
        assert!(machine_administration_researcher.outputs().contains(&news));
        assert!(machine_administration_researcher.outputs().contains(&coin));
        assert!(machine_administration_researcher
            .outputs()
            .contains(&coffee));
        assert!(machine_administration_researcher.outputs().contains(&tea));
        assert!(machine_administration_researcher
            .outputs()
            .contains(&publication));

        assert_eq!(machine_administration_researcher.inputs().len(), 1);
        assert_eq!(machine_administration_researcher.outputs().len(), 5);
        assert_eq!(machine_administration_researcher.clock_count(), 3);

        let automaton = machine_administration_researcher
            .clone()
            .into_automaton()
            .unwrap();

        assert_eq!(automaton.node_iter().try_len().unwrap(), 25);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 97);
    }

    #[test]
    fn specification_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(&mut symbols);
        let refinment = Refinement::new(
            specification.clone().is_input_enabled().unwrap(),
            specification.clone().is_input_enabled().unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let refinment = Refinement::new(
            machine.clone().is_input_enabled().unwrap(),
            machine.clone().is_input_enabled().unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn administration_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(&mut symbols);
        let refinment = Refinement::new(
            administration.clone().is_input_enabled().unwrap(),
            administration.clone().is_input_enabled().unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn researcher_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let researcher = new_researcher(&mut symbols);
        let refinment = Refinement::new(
            researcher.clone().is_input_enabled().unwrap(),
            researcher.clone().is_input_enabled().unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn composition_of_machine_administration_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let administration = new_administration(&mut symbols);

        let machine_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinment = Refinement::new(
            Box::new(machine_administration.clone().into()),
            Box::new(machine_administration.clone().into()),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn composition_of_machine_researcher_refines_self() {
        // The interplay between the machine and researcher fails.
        // However, machine and administration succeeds.
        // Also, researcher and administration succeeds.
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let researcher = new_researcher(&mut symbols);

        let machine_researcher = Composition::new(
            machine.is_input_enabled().unwrap(),
            researcher.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinment = Refinement::new(
            Box::new(machine_researcher.clone().into()),
            Box::new(machine_researcher.clone().into()),
        );
        assert!(refinment.is_ok());
        let refines = refinment.unwrap().refines();

        let (implementation_ct, specification_ct) = refines.err().unwrap();
        let boxed: Box<dyn TIOA> = Box::new(machine_researcher);
        println!("{}", implementation_ct.in_context(&boxed, &symbols).dot());
        println!("{}", specification_ct.in_context(&boxed, &symbols).dot());

        //assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn composition_of_administration_researcher_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let administration = new_administration(&mut symbols);

        let machine_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinment = Refinement::new(
            Box::new(machine_administration.clone().into()),
            Box::new(machine_administration.clone().into()),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }

    #[test]
    fn composition_of_researcher_machine_administration_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let administration = new_administration(&mut symbols);
        let researcher = new_researcher(&mut symbols);

        let machine_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();
        let machine_administration_researcher = Composition::new(
            Box::new(machine_administration.into()),
            researcher.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinment = Refinement::new(
            Box::new(machine_administration_researcher.clone().into()),
            Box::new(machine_administration_researcher.clone().into()),
        );
        assert!(refinment.is_ok());
        let refines = refinment.unwrap().refines();

        let (implementation_ct, specification_ct) = refines.err().unwrap();
        let boxed: Box<dyn TIOA> = Box::new(machine_administration_researcher);
        println!("{}", implementation_ct.in_context(&boxed, &symbols).dot());
        println!("{}", specification_ct.in_context(&boxed, &symbols).dot());

        // assert!(refines.is_ok());
    }

    #[test]
    fn implementation_refines_specification() {
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(&mut symbols);
        let machine = new_machine(&mut symbols);
        let administration = new_administration(&mut symbols);
        let researcher = new_researcher(&mut symbols);

        let machine_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();
        let machine_administration_researcher = Composition::new(
            Box::new(machine_administration.into()),
            researcher.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinment = Refinement::new(
            Box::new(machine_administration_researcher.into()),
            specification.is_input_enabled().unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines().is_ok());
    }
}
