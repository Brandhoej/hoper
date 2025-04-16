#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::automata::{
        automaton::{Automaton, IntoAutomaton},
        automaton_builder::AutomatonBuilder,
        composition::Composition,
        expressions::{Comparison, Expression},
        input_enabled::InputEnabled,
        partitioned_symbol_table::PartitionedSymbolTable,
        refinement::Refinement,
        statements::Statement,
    };

    fn new_specification(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let grant = builder.add_symbol(0, "grant");
        let news = builder.add_symbol(0, "news");

        // Local declarations:
        let clock = builder.add_clock(1, "u");
        let loc0_symbol = builder.add_symbol(1, "0");
        let loc1_symbol = builder.add_symbol(1, "1");
        let loc2_symbol = builder.add_symbol(1, "2");

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

    fn new_administration(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let grant = builder.add_symbol(0, "grant");
        let news = builder.add_symbol(0, "news");
        let publication = builder.add_symbol(0, "publication");
        let coin = builder.add_symbol(0, "coin");

        // Local declarations:
        let clock = builder.add_clock(2, "z");
        let loc0_symbol = builder.add_symbol(2, "0");
        let loc1_symbol = builder.add_symbol(2, "1");
        let loc2_symbol = builder.add_symbol(2, "2");
        let loc3_symbol = builder.add_symbol(2, "3");

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

    fn new_machine(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let tea = builder.add_symbol(0, "tea");
        let coffee = builder.add_symbol(0, "coffee");
        let coin = builder.add_symbol(0, "coin");

        // Local declarations:
        let clock = builder.add_clock(3, "y");
        let loc0_symbol = builder.add_symbol(3, "0");
        let loc1_symbol = builder.add_symbol(3, "1");

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

    pub fn new_researcher(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let tea = builder.add_symbol(0, "tea");
        let coffee = builder.add_symbol(0, "coffee");
        let publication = builder.add_symbol(0, "publication");

        // Local declarations:
        let clock = builder.add_clock(5, "x");
        let loc0_symbol = builder.add_symbol(5, "0");
        let loc1_symbol = builder.add_symbol(5, "1");
        let loc2_symbol = builder.add_symbol(5, "2");
        let loc3_symbol = builder.add_symbol(5, "3");

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
        let x_less_than_or_equal_4 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::LessThanOrEqual,
            4.into(),
        );
        let x_less_than_or_equal_8 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::LessThanOrEqual,
            8.into(),
        );
        let x_less_than_or_equal_15 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::LessThanOrEqual,
            15.into(),
        );
        let x_greater_than_15 = Expression::new_clock_constraint(
            clock.into(),
            Comparison::GreaterThan,
            15.into(),
        );

        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, None);
        let loc2 = builder.add_location(loc2_symbol, Some(x_less_than_or_equal_4));
        let loc3 = builder.add_location(loc3_symbol, Some(x_less_than_or_equal_8));
        builder.set_initial_location(loc0);

        builder.add_edge_input(loc0, loc1, tea, Some(x_greater_than_15), None);

        builder.add_edge_input(loc0, loc2, coffee, None, Some(reset_x.clone()));
        builder.add_edge_output(loc2, loc0, publication, Some(x_greater_than_or_equal_2), Some(reset_x.clone()));

        builder.add_edge_input(loc0, loc3, tea, Some(x_less_than_or_equal_15), Some(reset_x.clone()));
        builder.add_edge_output(loc3, loc0, publication, Some(x_greater_than_or_equal_4), Some(reset_x.clone()));
        
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
        let specification = new_specification(&mut symbols);

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
        let administration = new_administration(&mut symbols);

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
        let machine = new_machine(&mut symbols);

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
        let researcher = new_researcher(&mut symbols);

        let contextual_automaton = researcher.in_context(&symbols);
        println!("{}", contextual_automaton.dot());

        assert_eq!(researcher.inputs().try_len().unwrap(), 2);
        assert_eq!(researcher.outputs().try_len().unwrap(), 1);
        assert_eq!(researcher.node_iter().try_len().unwrap(), 4);
        assert_eq!(researcher.edge_iter().try_len().unwrap(), 12);
    }

    #[test]
    fn specification_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let specification = new_specification(&mut symbols);

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
        let administration = new_administration(&mut symbols);

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
        let specification = new_specification(&mut symbols);
        let administration = new_administration(&mut symbols);
        let composition = Composition::new(
            administration.is_input_enabled().unwrap(),
            specification.is_input_enabled().unwrap(),
        );

        assert!(composition.is_err());
    }

    #[test]
    fn machine_researcher() {
        // FAILS!
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let composition = Composition::new(
            machine.is_input_enabled().unwrap(),
            researcher.is_input_enabled().unwrap(),
        ).unwrap();
        let automaton = composition.into_automaton().unwrap();

        let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());
    }

    #[test]
    fn machine_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);

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
        let researcher = new_researcher(&mut symbols);

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
        let machine = new_machine(&mut symbols);
        let administration = new_administration(&mut symbols);
        let composition = Composition::new(
            administration.is_input_enabled().unwrap(),
            machine.is_input_enabled().unwrap(),
        ).unwrap();

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
        let mut symbols = PartitionedSymbolTable::new();
        let machine = new_machine(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let composition = Composition::new(
            researcher.is_input_enabled().unwrap(),
            machine.is_input_enabled().unwrap(),
        ).unwrap();

        let refinement = Refinement::new(
            Box::new(composition.clone().into()),
            Box::new(composition.clone().into()),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_ok());
    }

    #[test]
    fn administration_researcher_refines_self() {
        let mut symbols = PartitionedSymbolTable::new();
        let administration = new_administration(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let composition = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        ).unwrap();

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
        let administration = new_administration(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let machine = new_machine(&mut symbols);
        let researcher_administration = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        ).unwrap();
        let machine_researcher_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            Box::new(researcher_administration.into()),
        ).unwrap();

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
        let administration = new_administration(&mut symbols);
        let researcher = new_researcher(&mut symbols);
        let machine = new_machine(&mut symbols);
        let researcher_administration = Composition::new(
            researcher.is_input_enabled().unwrap(),
            administration.is_input_enabled().unwrap(),
        ).unwrap();
        let machine_researcher_administration = Composition::new(
            machine.is_input_enabled().unwrap(),
            Box::new(researcher_administration.into()),
        ).unwrap();
        let specification = new_specification(&mut symbols);

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
        let machine = new_machine(&mut symbols);
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
        let machine = new_machine(&mut symbols);
        let machine_specification = new_machine_specification(&mut symbols);

        let refinement = Refinement::new(
            machine.clone().is_input_enabled().unwrap(),
            machine_specification.clone().is_input_enabled().unwrap(),
        );

        assert!(refinement.is_ok());
        assert!(refinement.unwrap().refines().is_err());
    }
}
