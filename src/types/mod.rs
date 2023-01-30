use core::fmt;

pub type RawPageID = u16;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PageID {
    raw: RawPageID,
}

impl PageID {
    pub const fn from_raw(raw: RawPageID) -> Option<Self> {
        match raw {
            RawPageID::MAX => None,
            _ => Some(Self { raw }),
        }
    }

    pub const fn into_raw(self) -> RawPageID {
        self.raw
    }

    pub const fn index(self) -> usize {
        self.raw as usize
    }
}

impl fmt::Debug for PageID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.raw)
    }
}

#[cfg(feature = "defmt")]
impl defmt::Format for PageID {
    fn format(&self, fmt: defmt::Formatter) {
        defmt::write!(fmt, "{=u16}", self.raw)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct OptionPageID {
    raw: RawPageID,
}

impl OptionPageID {
    pub const fn none() -> Self {
        Self { raw: RawPageID::MAX }
    }

    pub const fn some(page_id: PageID) -> Self {
        Self { raw: page_id.raw }
    }

    pub const fn from_raw(raw: RawPageID) -> Self {
        Self { raw }
    }

    pub const fn into_raw(self) -> RawPageID {
        self.raw
    }

    pub const fn from_option(o: Option<PageID>) -> Self {
        match o {
            Some(p) => Self { raw: p.raw },
            None => Self::none(),
        }
    }

    pub const fn into_option(self) -> Option<PageID> {
        PageID::from_raw(self.raw)
    }

    pub const fn is_some(self) -> bool {
        self.raw != RawPageID::MAX
    }

    pub const fn is_none(self) -> bool {
        self.raw == RawPageID::MAX
    }
}

impl From<PageID> for OptionPageID {
    fn from(value: PageID) -> Self {
        Self { raw: value.raw }
    }
}

impl From<Option<PageID>> for OptionPageID {
    fn from(value: Option<PageID>) -> Self {
        Self::from_option(value)
    }
}

impl From<OptionPageID> for Option<PageID> {
    fn from(value: OptionPageID) -> Self {
        value.into_option()
    }
}

impl fmt::Debug for OptionPageID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.into_option())
    }
}

#[cfg(feature = "defmt")]
impl defmt::Format for OptionPageID {
    fn format(&self, fmt: defmt::Formatter) {
        defmt::write!(fmt, "{:?}", self.into_option())
    }
}
