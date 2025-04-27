#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::automata::{
        action::Action,
        automaton::{Automaton, IntoAutomaton},
        automaton_builder::AutomatonBuilder,
        channel::Channel,
        composition::Composition,
        expressions::{Comparison, Expression},
        input_enabled::InputEnabled,
        ioa::IOA,
        partitioned_symbol_table::PartitionedSymbolTable,
        refinement::Refinement,
        statements::Statement,
    };

    fn new_specification(partition: u32, symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let grant = builder.add_symbol(0, "grant");
        let news = builder.add_symbol(0, "news");

        // Local declarations:
        let clock = builder.add_clock(partition, "u");
        let loc0_symbol = builder.add_symbol(partition, "0");
        let loc1_symbol = builder.add_symbol(partition, "1");
        let loc2_symbol = builder.add_symbol(partition, "2");

        // Build
        let reset_u = Statement::reset(clock, 0);
        let u_greater_than_2 =
            Expression::new_clock_constraint(clock.into(), Comparison::GreaterThan, 2.into());
        let u_less_than_or_equal_2 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 2.into());
        let u_less_than_or_equal_20 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 20.into());

        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, None);
        let loc2 = builder.add_location(loc2_symbol, Some(u_less_than_or_equal_20.clone()));
        builder.set_initial_location(loc0);

        builder.add_edge_input(loc1, loc1, grant, None, None);
        builder.add_edge_output(loc1, loc1, news, None, None);
        builder.add_edge_input(loc0, loc1, grant, Some(u_greater_than_2.clone()), None);
        builder.add_edge_input(
            loc0,
            loc2,
            grant,
            Some(u_less_than_or_equal_2.clone()),
            Some(reset_u.clone()),
        );
        builder.add_edge_output(loc2, loc0, news, None, Some(reset_u.clone()));
        builder.add_edge_input(loc2, loc2, grant, None, None);

        builder.build().unwrap()
    }

    fn new_administration(partition: u32, symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let grant = builder.add_symbol(0, "grant");
        let news = builder.add_symbol(0, "news");
        let publication = builder.add_symbol(0, "publication");
        let coin = builder.add_symbol(0, "coin");

        // Local declarations:
        let clock = builder.add_clock(partition, "z");
        let loc0_symbol = builder.add_symbol(partition, "0");
        let loc1_symbol = builder.add_symbol(partition, "1");
        let loc2_symbol = builder.add_symbol(partition, "2");
        let loc3_symbol = builder.add_symbol(partition, "3");

        // Build
        let reset_z = Statement::reset(clock, 0);
        let z_less_than_2 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThan, 2.into());

        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, Some(z_less_than_2.clone()));
        let loc2 = builder.add_location(loc2_symbol, Some(z_less_than_2.clone()));
        let loc3 = builder.add_location(loc3_symbol, None);
        builder.set_initial_location(loc0);

        builder.add_edge_input(loc0, loc1, grant, None, Some(reset_z.clone()));
        builder.add_edge_input(loc1, loc1, grant, None, None);
        builder.add_edge_input(loc1, loc1, publication, None, None);
        builder.add_edge_output(loc1, loc3, coin, None, None);
        builder.add_edge_input(loc3, loc3, grant, None, None);
        builder.add_edge_input(loc3, loc2, publication, None, Some(reset_z.clone()));
        builder.add_edge_input(loc2, loc2, grant, None, None);
        builder.add_edge_input(loc2, loc2, publication, None, None);
        builder.add_edge_input(loc0, loc2, publication, None, Some(reset_z));
        builder.add_edge_output(loc2, loc0, news, None, None);

        builder.build().unwrap()
    }

    fn new_machine(partition: u32, symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let tea = builder.add_symbol(0, "tea");
        let coffee = builder.add_symbol(0, "coffee");
        let coin = builder.add_symbol(0, "coin");

        // Local declarations:
        let clock = builder.add_clock(partition, "y");
        let loc0_symbol = builder.add_symbol(partition, "0");
        let loc1_symbol = builder.add_symbol(partition, "1");

        // Build
        let reset_y = Statement::reset(clock, 0);
        let y_less_than_or_equal_6 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 6.into());
        let y_greater_than_or_equal_4 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThanOrEqual,
            4.into(),
        );
        let y_greater_than_or_equal_2 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThanOrEqual,
            2.into(),
        );

        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, Some(y_less_than_or_equal_6));
        builder.set_initial_location(loc0);

        builder.add_edge_output(
            loc0,
            loc0,
            tea,
            Some(y_greater_than_or_equal_2.clone()),
            None,
        );
        builder.add_edge_input(loc0, loc1, coin, None, Some(reset_y.clone()));
        builder.add_edge_input(loc1, loc1, coin, None, None);
        builder.add_edge_output(
            loc1,
            loc0,
            coffee,
            Some(y_greater_than_or_equal_4.clone()),
            None,
        );
        builder.add_edge_output(loc1, loc0, tea, None, None);

        builder.build().unwrap()
    }

    pub fn new_machine_specification(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let tea = builder.add_symbol(0, "tea");
        let coffee = builder.add_symbol(0, "coffee");
        let coin = builder.add_symbol(0, "coin");

        // Local declarations:
        let clock = builder.add_clock(4, "y");
        let loc0_symbol = builder.add_symbol(4, "0");
        let loc1_symbol = builder.add_symbol(4, "1");

        // Build
        let reset_y = Statement::reset(clock, 0);
        let y_less_than_or_equal_5 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 5.into());
        let y_greater_than_or_equal_4 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThanOrEqual,
            4.into(),
        );
        let y_greater_than_or_equal_2 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThanOrEqual,
            2.into(),
        );

        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, Some(y_less_than_or_equal_5));
        builder.set_initial_location(loc0);

        builder.add_edge_output(loc0, loc0, tea, Some(y_greater_than_or_equal_2), None);
        builder.add_edge_input(loc0, loc1, coin, None, Some(reset_y));
        builder.add_edge_input(loc1, loc1, coin, None, None);
        builder.add_edge_output(loc1, loc0, coffee, Some(y_greater_than_or_equal_4), None);

        builder.build().unwrap()
    }

    pub fn new_researcher(partition: u32, symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let tea = builder.add_symbol(0, "tea");
        let coffee = builder.add_symbol(0, "coffee");
        let publication = builder.add_symbol(0, "publication");

        // Local declarations:
        let clock = builder.add_clock(partition, "x");
        let loc0_symbol = builder.add_symbol(partition, "0");
        let loc1_symbol = builder.add_symbol(partition, "1");
        let loc2_symbol = builder.add_symbol(partition, "2");
        let loc3_symbol = builder.add_symbol(partition, "3");

        // Build
        let reset_x = Statement::reset(clock, 0);
        let x_greater_than_or_equal_2 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThanOrEqual,
            2.into(),
        );
        let x_greater_than_or_equal_4 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThanOrEqual,
            4.into(),
        );
        let x_less_than_or_equal_4 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 4.into());
        let x_less_than_or_equal_8 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 8.into());
        let x_less_than_or_equal_15 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 15.into());
        let x_greater_than_15 =
            Expression::new_clock_constraint(clock.into(), Comparison::GreaterThan, 15.into());

        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, None);
        let loc2 = builder.add_location(loc2_symbol, Some(x_less_than_or_equal_4));
        let loc3 = builder.add_location(loc3_symbol, Some(x_less_than_or_equal_8));
        builder.set_initial_location(loc0);

        builder.add_edge_input(loc0, loc1, tea, Some(x_greater_than_15), None);

        builder.add_edge_input(loc0, loc2, coffee, None, Some(reset_x.clone()));
        builder.add_edge_output(
            loc2,
            loc0,
            publication,
            Some(x_greater_than_or_equal_2),
            Some(reset_x.clone()),
        );

        builder.add_edge_input(
            loc0,
            loc3,
            tea,
            Some(x_less_than_or_equal_15),
            Some(reset_x.clone()),
        );
        builder.add_edge_output(
            loc3,
            loc0,
            publication,
            Some(x_greater_than_or_equal_4),
            Some(reset_x.clone()),
        );

        builder.add_edge_input(loc1, loc1, coffee, None, None);
        builder.add_edge_input(loc1, loc1, tea, None, None);
        builder.add_edge_output(loc1, loc1, publication, None, None);

        builder.add_edge_input(loc2, loc2, coffee, None, None);
        builder.add_edge_input(loc2, loc2, tea, None, None);

        builder.add_edge_input(loc3, loc3, coffee, None, None);
        builder.add_edge_input(loc3, loc3, tea, None, None);

        builder.build().unwrap()
    }

    #[test]
    fn specification() {
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(1, &mut symbols);

        /*let contextual_automaton = specification.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(specification.inputs().try_len().unwrap(), 1);
        assert_eq!(specification.outputs().try_len().unwrap(), 1);
        assert_eq!(specification.node_iter().try_len().unwrap(), 3);
        assert_eq!(specification.edge_iter().try_len().unwrap(), 6);
    }

    #[test]
    fn administration() {
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(2, &mut symbols);

        /*let contextual_automaton = administration.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(administration.inputs().try_len().unwrap(), 2);
        assert_eq!(administration.outputs().try_len().unwrap(), 2);
        assert_eq!(administration.node_iter().try_len().unwrap(), 4);
        assert_eq!(administration.edge_iter().try_len().unwrap(), 10);
    }

    #[test]
    fn machine() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(3, &mut symbols);

        let contextual_automaton = machine.in_context(&symbols);
        println!("{}", contextual_automaton.dot());

        assert_eq!(machine.inputs().try_len().unwrap(), 1);
        assert_eq!(machine.outputs().try_len().unwrap(), 2);
        assert_eq!(machine.node_iter().try_len().unwrap(), 2);
        assert_eq!(machine.edge_iter().try_len().unwrap(), 5);
    }

    #[test]
    fn machine_specification() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine_specification = new_machine_specification(&mut symbols);

        /*let contextual_automaton = machine_specification.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(machine_specification.inputs().try_len().unwrap(), 1);
        assert_eq!(machine_specification.outputs().try_len().unwrap(), 2);
        assert_eq!(machine_specification.node_iter().try_len().unwrap(), 2);
        assert_eq!(machine_specification.edge_iter().try_len().unwrap(), 4);
    }

    #[test]
    fn researcher() {
        let mut symbols = PartitionedSymbolTable::new();
        let researcher = new_researcher(5, &mut symbols);

        let contextual_automaton = researcher.in_context(&symbols);
        println!("{}", contextual_automaton.dot());

        assert_eq!(researcher.inputs().try_len().unwrap(), 2);
        assert_eq!(researcher.outputs().try_len().unwrap(), 1);
        assert_eq!(researcher.node_iter().try_len().unwrap(), 4);
        assert_eq!(researcher.edge_iter().try_len().unwrap(), 12);
    }

    #[test]
    fn machine_researcher() {
        let mut symbols = PartitionedSymbolTable::new();
        let publication = symbols.intern(0, "publication");
        let coin = symbols.intern(0, "coin");
        let tea = symbols.intern(0, "tea");
        let coffee = symbols.intern(0, "coffee");

        let researcher_loc0_symbol = symbols.intern(5, "0");
        let researcher_loc1_symbol = symbols.intern(5, "1");
        let researcher_loc2_symbol = symbols.intern(5, "2");
        let researcher_loc3_symbol = symbols.intern(5, "3");
        assert_ne!(researcher_loc0_symbol, researcher_loc1_symbol);
        assert_ne!(researcher_loc1_symbol, researcher_loc2_symbol);
        assert_ne!(researcher_loc2_symbol, researcher_loc3_symbol);

        let machine_loc0_symbol = symbols.intern(3, "0");
        let machine_loc1_symbol = symbols.intern(3, "1");
        assert_ne!(machine_loc0_symbol, researcher_loc0_symbol);
        assert_ne!(machine_loc0_symbol, machine_loc1_symbol);

        let researcher = new_researcher(5, &mut symbols);
        let machine = new_machine(3, &mut symbols);
        let composition = Composition::new(
            researcher.is_input_enabled().unwrap(),
            machine.is_input_enabled().unwrap(),
        )
        .unwrap();

        assert_eq!(composition.common_actions().try_len().unwrap(), 2);
        assert!(composition.common_actions().contains(&Action::new(tea)));
        assert!(composition.common_actions().contains(&Action::new(coffee)));

        assert_eq!(composition.lhs_unique_actions().try_len().unwrap(), 1);
        assert!(composition
            .lhs_unique_actions()
            .contains(&Action::new(publication)));

        assert_eq!(composition.rhs_unique_actions().try_len().unwrap(), 1);
        assert!(composition
            .rhs_unique_actions()
            .contains(&Action::new(coin)));

        assert_eq!(composition.inputs().len(), 1);
        assert!(composition.inputs().contains(&Action::new(coin)));

        assert_eq!(composition.outputs().len(), 3);
        assert!(composition.outputs().contains(&Action::new(publication)));
        assert!(composition.outputs().contains(&Action::new(coffee)));
        assert!(composition.outputs().contains(&Action::new(tea)));

        assert_eq!(composition.actions().len(), 4);
        assert!(composition.actions().contains(&Action::new(publication)));
        assert!(composition.actions().contains(&Action::new(coffee)));
        assert!(composition.actions().contains(&Action::new(tea)));
        assert!(composition.actions().contains(&Action::new(coin)));

        assert_eq!(composition.channels().len(), 4);
        assert!(composition
            .channels()
            .contains(&Channel::Out(Action::new(publication))));
        assert!(composition
            .channels()
            .contains(&Channel::Out(Action::new(coffee))));
        assert!(composition
            .channels()
            .contains(&Channel::Out(Action::new(tea))));
        assert!(composition
            .channels()
            .contains(&Channel::In(Action::new(coin))));

        let automaton = composition.into_automaton().unwrap();
        let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());

        assert_eq!(automaton.inputs().try_len().unwrap(), 1);
        assert!(automaton.inputs().contains(&Action::new(coin)));

        assert_eq!(automaton.outputs().try_len().unwrap(), 3);
        assert!(automaton.outputs().contains(&Action::new(publication)));
        assert!(automaton.outputs().contains(&Action::new(tea)));
        assert!(automaton.outputs().contains(&Action::new(coffee)));

        assert_eq!(automaton.node_iter().try_len().unwrap(), 8);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 28);
    }

    #[test]
    fn specification_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(1, &mut symbols);

        let refinement = Refinement::new(
            specification.clone().is_input_enabled().unwrap(),
            specification.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn administration_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(2, &mut symbols);

        let refinement = Refinement::new(
            administration.clone().is_input_enabled().unwrap(),
            administration.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn specification_administration() {
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(1, &mut symbols);
        let administration = new_administration(2, &mut symbols);
        let composition = Composition::new(
            administration.is_input_enabled().unwrap(),
            specification.is_input_enabled().unwrap(),
        );

        assert!(composition.is_err());
    }

    #[test]
    fn machine_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(3, &mut symbols);

        let refinement = Refinement::new(
            machine.clone().is_input_enabled().unwrap(),
            machine.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn researcher_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let researcher = new_researcher(5, &mut symbols);

        let refinement = Refinement::new(
            researcher.clone().is_input_enabled().unwrap(),
            researcher.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_administration_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(3, &mut symbols);
        let administration = new_administration(2, &mut symbols);
        let composition = Composition::new(
            administration.is_input_enabled().unwrap(),
            machine.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinement = Refinement::new(
            Box::new(composition.clone().into()),
            Box::new(composition.clone().into()),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_researcher_refines_self() {
        // FAILS!
        // I believe the reason is that the researcher can move from 0 to 3 and 0 to 1 which should not be possible.
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(3, &mut symbols);
        let researcher = new_researcher(5, &mut symbols);
        let composition = Composition::new(
            researcher.is_input_enabled().unwrap(),
            machine.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinement = Refinement::new(
            Box::new(composition.clone().into()),
            Box::new(composition.clone().into()),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn administration_researcher_refines_self() {
        // FAILS!
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(2, &mut symbols);
        let researcher = new_researcher(5, &mut symbols);
        let composition = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();

        let refinement = Refinement::new(
            Box::new(composition.clone().into()),
            Box::new(composition.clone().into()),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_administration_researcher_refines_self() {
        // FAILS! Same as "machine_researcher"
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(2, &mut symbols);
        let researcher = new_researcher(5, &mut symbols);
        let machine = new_machine(3, &mut symbols);
        let researcher_administration = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();
        let machine_researcher_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            Box::new(researcher_administration.into()),
        )
        .unwrap();

        let refinement = Refinement::new(
            Box::new(machine_researcher_administration.clone().into()),
            Box::new(machine_researcher_administration.clone().into()),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_administration_researcher_refines_specification() {
        // FAILS!
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(2, &mut symbols);
        let researcher = new_researcher(5, &mut symbols);
        let machine = new_machine(3, &mut symbols);
        let researcher_administration = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();
        let machine_researcher_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            Box::new(researcher_administration.into()),
        )
        .unwrap();
        let specification = new_specification(1, &mut symbols);

        let refinement = Refinement::new(
            Box::new(machine_researcher_administration.clone().into()),
            specification.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_specification_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine_specification = new_machine_specification(&mut symbols);

        let refinement = Refinement::new(
            machine_specification.clone().is_input_enabled().unwrap(),
            machine_specification.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_specification_refines_machine() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(3, &mut symbols);
        let machine_specification = new_machine_specification(&mut symbols);

        let refinement = Refinement::new(
            machine_specification.clone().is_input_enabled().unwrap(),
            machine.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn machine_refines_machine_specification() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(3, &mut symbols);
        let machine_specification = new_machine_specification(&mut symbols);

        let refinement = Refinement::new(
            machine.clone().is_input_enabled().unwrap(),
            machine_specification.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_err());
    }

    #[test]
    fn machine_administration_machine_refines_specification() {
        let mut symbols = PartitionedSymbolTable::new();
        let grant = symbols.intern(0, "grant");
        let news = symbols.intern(0, "news");
        let publication = symbols.intern(0, "publication");
        let coin = symbols.intern(0, "coin");
        let tea = symbols.intern(0, "tea");
        let coffee = symbols.intern(0, "coffee");

        let administration = new_administration(2, &mut symbols);
        let researcher = new_researcher(5, &mut symbols);
        let machine = new_machine(3, &mut symbols);
        let researcher_administration = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        )
        .unwrap();
        let machine_researcher_administration = Composition::new(
            Box::new(researcher_administration.into()),
            machine.is_input_enabled().unwrap(),
        )
        .unwrap();

        let specification = new_specification(1, &mut symbols);

        assert_eq!(1, specification.inputs().try_len().unwrap());
        assert!(specification.inputs().contains(&Action::new(grant)));

        assert_eq!(1, specification.outputs().try_len().unwrap());
        assert!(specification.outputs().contains(&Action::new(news)));

        assert_eq!(
            3,
            machine_researcher_administration
                .common_actions()
                .try_len()
                .unwrap()
        );
        assert!(machine_researcher_administration
            .common_actions()
            .contains(&Action::new(coin)));
        assert!(machine_researcher_administration
            .common_actions()
            .contains(&Action::new(tea)));
        assert!(machine_researcher_administration
            .common_actions()
            .contains(&Action::new(coffee)));

        assert_eq!(
            3,
            machine_researcher_administration
                .lhs_unique_actions()
                .try_len()
                .unwrap()
        );
        assert!(machine_researcher_administration
            .lhs_unique_actions()
            .contains(&Action::new(grant)));
        assert!(machine_researcher_administration
            .lhs_unique_actions()
            .contains(&Action::new(news)));
        assert!(machine_researcher_administration
            .lhs_unique_actions()
            .contains(&Action::new(publication)));

        assert_eq!(
            0,
            machine_researcher_administration
                .rhs_unique_actions()
                .try_len()
                .unwrap()
        );

        assert_eq!(1, machine_researcher_administration.inputs().len());
        assert!(machine_researcher_administration
            .inputs()
            .contains(&Action::new(grant)));

        assert_eq!(5, machine_researcher_administration.outputs().len());
        assert!(machine_researcher_administration
            .outputs()
            .contains(&Action::new(news)));
        assert!(machine_researcher_administration
            .outputs()
            .contains(&Action::new(publication)));
        assert!(machine_researcher_administration
            .outputs()
            .contains(&Action::new(coin)));
        assert!(machine_researcher_administration
            .outputs()
            .contains(&Action::new(tea)));
        assert!(machine_researcher_administration
            .outputs()
            .contains(&Action::new(coffee)));

        let refinement = Refinement::new(
            Box::new(machine_researcher_administration.clone().into()),
            specification.clone().is_input_enabled().unwrap(),
        )
        .unwrap();

        assert_eq!(1, refinement.common_inputs().try_len().unwrap());
        assert!(refinement.common_inputs().contains(&Action::new(grant)));

        assert_eq!(1, refinement.common_outputs().try_len().unwrap());
        assert!(refinement.common_outputs().contains(&Action::new(news)));

        assert_eq!(
            0,
            refinement.unique_specification_inputs().try_len().unwrap()
        );

        assert_eq!(
            4,
            refinement
                .unique_implementation_outputs()
                .try_len()
                .unwrap()
        );
        assert!(refinement
            .unique_implementation_outputs()
            .contains(&Action::new(publication)));
        assert!(refinement
            .unique_implementation_outputs()
            .contains(&Action::new(coffee)));
        assert!(refinement
            .unique_implementation_outputs()
            .contains(&Action::new(tea)));
        assert!(refinement
            .unique_implementation_outputs()
            .contains(&Action::new(coin)));

        assert!(refinement.refines().is_ok());
    }
}
